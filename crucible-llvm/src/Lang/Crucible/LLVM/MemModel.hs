------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel
-- Description      : Core definitions of the symbolic C memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyDataDecls #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.LLVM.MemModel
  ( -- * Memories
    Mem
  , memRepr
  , MemImpl
  , emptyMem
  , memEndian
  , ppMem
  , doDumpMem
  , mkMemVar

    -- * Pointers
  , LLVMPointerType
  , pattern LLVMPointerRepr
  , pattern PtrRepr
  , LLVMPtr
  , pattern LLVMPointer
  , llvmPointerView
  , ptrWidth
  , G.ppPtr
  , llvmPointer_bv
  , projectLLVM_bv

    -- * Memory operations
  , doMalloc
  , G.AllocType(..)
  , G.Mutability(..)
  , doMallocHandle
  , doLookupHandle
  , doMemcpy
  , doMemset
  , doCalloc
  , doFree
  , doLoad
  , doStore
  , loadString
  , loadMaybeString
  , doResolveGlobal
  , registerGlobal
  , allocGlobals

    -- * \"Raw\" operations with LLVMVal
  , LLVMVal(..)
  , FloatSize(..)
  , unpackMemValue
  , packMemValue
  , loadRaw
  , loadRawWithCondition
  , storeRaw
  , storeConstRaw
  , mallocRaw
  , mallocConstRaw
  , constToLLVMVal

    -- * Storage types
  , G.Type
  , G.typeF
  , G.TypeF(..)
  , G.Field
  , G.typeSize
  , G.fieldVal
  , G.fieldPad
  , G.bitvectorType
  , G.arrayType
  , G.mkStructType
  , G.floatType
  , G.doubleType
  , toStorableType

    -- * Pointer operations
  , ptrToPtrVal
  , mkNullPointer
  , ptrIsNull
  , ptrEq
  , ptrAdd
  , ptrSub
  , ptrDiff
  , doPtrAddOffset
  , doPtrSubtract
  , isValidPointer
  , muxLLVMPtr

    -- * Disjointness
  , assertDisjointRegions
  , assertDisjointRegions'
  , buildDisjointRegionsAssertion

    -- * PtrWidth
  , HasPtrWidth
  , pattern PtrWidth
  , withPtrWidth

    -- * Misc
  , llvmStatementExec
  , coerceAny
  , GlobalSymbol(..)
  , SomeFnHandle(..)
  ) where

import           Control.Lens hiding (Empty, (:>))
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Control.Monad.Trans(lift)
import           Control.Monad.Trans.State
import           Data.Dynamic
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Word
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import           GHC.TypeLits

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L

import           What4.ProgramLoc
import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.Partial

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.MemType
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemModel.Value
import           Lang.Crucible.LLVM.Translation.Constant
import           Lang.Crucible.LLVM.Types
import           Lang.Crucible.Panic(panic)

import GHC.Stack

--import Debug.Trace as Debug

instance IntrinsicClass sym "LLVM_memory" where
  type Intrinsic sym "LLVM_memory" ctx = MemImpl sym

  -- NB: Here we are assuming the global maps of both memories are identical.
  -- This should be the case as memories are only supposed to allocate globals at
  -- startup, not during program execution.  We could check that the maps match,
  -- but that would be expensive...
  muxIntrinsic _sym _iTypes _nm _ p mem1 mem2 =
     do let MemImpl blockSource gMap1 hMap1 m1 = mem1
        let MemImpl _blockSource _gMap2 hMap2 m2 = mem2
        --putStrLn "MEM MERGE"
        return $ MemImpl blockSource gMap1
                   (Map.union hMap1 hMap2)
                   (G.mergeMem p m1 m2)

  pushBranchIntrinsic _sym _iTypes _nm _ctx mem =
     do let MemImpl nxt gMap hMap m = mem
        --putStrLn "MEM PUSH BRANCH"
        return $ MemImpl nxt gMap hMap $ G.branchMem m

  abortBranchIntrinsic _sym _iTypes _nm _ctx mem =
     do let MemImpl nxt gMap hMap m = mem
        --putStrLn "MEM ABORT BRANCH"
        return $ MemImpl nxt gMap hMap $ G.branchAbortMem m

-- | Top-level evaluation function for LLVM extension statements.
--   LLVM extension statements are used to implement the memory model operations.
llvmStatementExec :: HasPtrWidth (ArchWidth arch) => EvalStmtFunc p sym (LLVM arch)
llvmStatementExec stmt cst =
  let sym = cst^.stateSymInterface
   in stateSolverProof cst (runStateT (evalStmt sym stmt) cst)

type EvalM p sym ext rtp blocks ret args a =
  StateT (CrucibleState p sym ext rtp blocks ret args) IO a

-- | Actual workhorse function for evaluating LLVM extension statements.
--   The semantics are explicitly organized as a state transformer monad
--   that modifes the global state of the simulator; this captures the
--   memory accessing effects of these statements.
evalStmt :: forall p sym ext rtp blocks ret args wptr tp.
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  LLVMStmt wptr (RegEntry sym) tp ->
  EvalM p sym ext rtp blocks ret args (RegValue sym tp)
evalStmt sym = eval
 where
  getMem :: GlobalVar Mem ->
            EvalM p sym ext rtp blocks ret args (MemImpl sym)
  getMem mvar =
    do gs <- use (stateTree.actFrame.gpGlobals)
       case lookupGlobal mvar gs of
         Just mem -> return mem
         Nothing  ->
           panic "MemModel.evalStmt.getMem"
             [ "Global heap value not initialized."
             , "*** Global heap variable: " ++ show mvar
             ]

  setMem :: GlobalVar Mem ->
            MemImpl sym ->
            EvalM p sym ext rtp blocks ret args ()
  setMem mvar mem = stateTree.actFrame.gpGlobals %= insertGlobal mvar mem

  failedAssert :: String -> EvalM p sym ext rtp blocks ret args a
  failedAssert = lift . addFailedAssertion sym . AssertFailureSimError

  eval :: LLVMStmt wptr (RegEntry sym) tp ->
          EvalM p sym ext rtp blocks ret args (RegValue sym tp)
  eval (LLVM_PushFrame mvar) =
     do mem <- getMem mvar
        let heap' = G.pushStackFrameMem (memImplHeap mem)
        setMem mvar mem{ memImplHeap = heap' }

  eval (LLVM_PopFrame mvar) =
     do mem <- getMem mvar
        let heap' = G.popStackFrameMem (memImplHeap mem)
        setMem mvar mem{ memImplHeap = heap' }

  eval (LLVM_Alloca _w mvar (regValue -> sz) loc) =
     do mem <- getMem mvar
        blkNum <- liftIO $ nextBlock (memImplBlockSource mem)
        blk <- liftIO $ natLit sym (fromIntegral blkNum)
        z <- liftIO $ bvLit sym PtrWidth 0

        let heap' = G.allocMem G.StackAlloc (fromInteger blkNum) sz G.Mutable (show loc) (memImplHeap mem)
        let ptr = LLVMPointer blk z

        setMem mvar mem{ memImplHeap = heap' }
        return ptr

  eval (LLVM_Load mvar (regValue -> ptr) tpr valType alignment) =
     do mem <- getMem mvar
        liftIO $ (coerceAny sym tpr =<< doLoad sym mem ptr valType alignment)

  eval (LLVM_MemClear mvar (regValue -> ptr) bytes) =
    do mem <- getMem mvar
       z   <- liftIO $ bvLit sym knownNat 0
       len <- liftIO $ bvLit sym PtrWidth (bytesToInteger bytes)
       mem' <- liftIO $ doMemset sym PtrWidth mem ptr z len
       setMem mvar mem'

  eval (LLVM_Store mvar (regValue -> ptr) tpr valType _alignment (regValue -> val)) =
     do mem <- getMem mvar
        mem' <- liftIO $ doStore sym mem ptr tpr valType val
        setMem mvar mem'

  eval (LLVM_LoadHandle mvar (regValue -> ptr) args ret) =
     do mem <- getMem mvar
        mhandle <- liftIO $ doLookupHandle sym mem ptr
        case mhandle of
           Left doc -> failedAssert (show doc)
           Right (SomeFnHandle h)
             | Just Refl <- testEquality handleTp expectedTp -> return (HandleFnVal h)
             | otherwise -> failedAssert
                 $ unlines ["Expected function handle of type " ++
                                                              show expectedTp
                           ,"but found handle of type " ++ show handleTp]
            where handleTp   = FunctionHandleRepr (handleArgTypes h) (handleReturnType h)
                  expectedTp = FunctionHandleRepr args ret

  eval (LLVM_ResolveGlobal _w mvar (GlobalSymbol symbol)) =
     do mem <- getMem mvar
        liftIO $ doResolveGlobal sym mem symbol

  eval (LLVM_PtrEq mvar (regValue -> x) (regValue -> y)) = do
     mem <- getMem mvar
     liftIO $ do
        let allocs_doc = G.ppAllocs (G.memAllocs (memImplHeap mem))
        let x_doc = G.ppPtr x
        let y_doc = G.ppPtr y

        v1 <- isValidPointer sym x mem
        v2 <- isValidPointer sym y mem
        v3 <- G.notAliasable sym x y (memImplHeap mem)
        assert sym v1
           (AssertFailureSimError $ unlines ["Invalid pointer compared for equality:", show x_doc, show allocs_doc])
        assert sym v2
           (AssertFailureSimError $ unlines ["Invalid pointer compared for equality:", show y_doc, show allocs_doc])
        assert sym v3
           (AssertFailureSimError $ unlines ["Const pointers compared for equality:", show x_doc, show y_doc, show allocs_doc])

        ptrEq sym PtrWidth x y

  eval (LLVM_PtrLe mvar (regValue -> x) (regValue -> y)) = do
    mem <- getMem mvar
    liftIO $ do
       let x_doc = G.ppPtr x
           y_doc = G.ppPtr y
       v1 <- isValidPointer sym x mem
       v2 <- isValidPointer sym y mem
       assert sym v1
          (AssertFailureSimError $ unwords ["Invalid pointer compared for ordering:", show x_doc])
       assert sym v2
          (AssertFailureSimError $ unwords ["Invalid pointer compared for ordering:", show y_doc])
       ptrLe sym PtrWidth x y

  eval (LLVM_PtrAddOffset _w mvar (regValue -> x) (regValue -> y)) =
    do mem <- getMem mvar
       liftIO $ doPtrAddOffset sym mem x y

  eval (LLVM_PtrSubtract _w mvar (regValue -> x) (regValue -> y)) =
    do mem <- getMem mvar
       liftIO $ doPtrSubtract sym mem x y

mkMemVar :: HandleAllocator s
         -> ST s (GlobalVar Mem)
mkMemVar halloc = freshGlobalVar halloc "llvm_memory" knownRepr

newtype BlockSource = BlockSource (IORef Integer)

nextBlock :: BlockSource -> IO Integer
nextBlock (BlockSource ref) =
  atomicModifyIORef' ref (\n -> (n+1, n))

-- | The implementation of an LLVM memory, containing an
-- allocation-block source, global map, handle map, and heap.
data MemImpl sym =
  MemImpl
  { memImplBlockSource :: BlockSource
  , memImplGlobalMap   :: GlobalMap sym
  , memImplHandleMap   :: Map Integer Dynamic
  , memImplHeap        :: G.Mem sym
  }

memEndian :: MemImpl sym -> EndianForm
memEndian = G.memEndian . memImplHeap

-- | Produce a fresh empty memory.
--   NB, we start counting allocation blocks at '1'.
--   Block number 0 is reserved for representing raw bitvectors.
emptyMem :: EndianForm -> IO (MemImpl sym)
emptyMem endianness = do
  blkRef <- newIORef 1
  return $ MemImpl (BlockSource blkRef) Map.empty Map.empty (G.emptyMem endianness)

data SomePointer sym = forall w. SomePointer !(LLVMPtr sym w)
type GlobalMap sym = Map L.Symbol (SomePointer sym)

-- | Allocate memory for each global, and register all the resulting
-- pointers in the global map.
allocGlobals :: (IsSymInterface sym, HasPtrWidth wptr)
             => sym
             -> [(L.Global, Bytes)]
             -> MemImpl sym
             -> IO (MemImpl sym)
allocGlobals sym gs mem = foldM (allocGlobal sym) mem gs

allocGlobal :: (IsSymInterface sym, HasPtrWidth wptr)
            => sym
            -> MemImpl sym
            -> (L.Global, Bytes)
            -> IO (MemImpl sym)
allocGlobal sym mem (g, sz) = do
  let symbol@(L.Symbol sym_str) = L.globalSym g
  let mut = if L.gaConstant (L.globalAttrs g) then G.Immutable else G.Mutable
  sz' <- bvLit sym PtrWidth (bytesToInteger sz)
  (ptr, mem') <- doMalloc sym G.GlobalAlloc mut sym_str mem sz'
  return (registerGlobal mem' symbol ptr)

-- | Add an entry to the global map of the given 'MemImpl'.
registerGlobal :: MemImpl sym -> L.Symbol -> LLVMPtr sym wptr -> MemImpl sym
registerGlobal (MemImpl blockSource gMap hMap mem) symbol ptr =
  let gMap' = Map.insert symbol (SomePointer ptr) gMap
  in MemImpl blockSource gMap' hMap mem

asCrucibleType
  :: G.Type
  -> (forall tpr. TypeRepr tpr -> x)
  -> x
asCrucibleType (G.Type tf _) k =
  case tf of
    G.Bitvector sz ->
       case someNat (bytesToBits sz) of
         Just (Some w)
           | Just LeqProof <- isPosNat w -> k (LLVMPointerRepr w)
         _ -> error $ unwords ["invalid bitvector size", show sz]
    G.Float  -> k (FloatRepr SingleFloatRepr)
    G.Double -> k (FloatRepr DoubleFloatRepr)
    G.Array _n t -> asCrucibleType t $ \tpr -> k (VectorRepr tpr)
    G.Struct xs -> go Ctx.empty (V.toList xs) $ \ctx -> k (StructRepr ctx)
      where go :: CtxRepr ctx0
               -> [G.Field G.Type]
               -> (forall ctx. CtxRepr ctx -> x)
               -> x
            go ctx [] k' = k' ctx
            go ctx (f:fs) k' =
                 asCrucibleType (f^.G.fieldVal) $ \tpr ->
                   go (ctx Ctx.:> tpr) fs k'

coerceAny :: (HasCallStack, IsSymInterface sym)
          => sym
          -> TypeRepr tpr
          -> AnyValue sym
          -> IO (RegValue sym tpr)
coerceAny sym tpr (AnyValue tpr' x)
  | Just Refl <- testEquality tpr tpr' = return x
  | otherwise =
    do loc <- getCurrentProgramLoc sym
       panic "coerceAny"
                  [ unwords ["Cannot coerce from", show tpr', "to", show tpr]
                  , "in: " ++ show (plFunction loc)
                  , "at: " ++ show (plSourceLoc loc)
                  ]

unpackZero ::
  (HasCallStack, IsSymInterface sym) =>
  sym ->
  G.Type ->
  IO (AnyValue sym)
unpackZero sym (G.Type tp _) = case tp of
  G.Bitvector bytes ->
    zeroInt sym bytes $ \case
      Nothing -> fail ("Improper storable type: " ++ show tp)
      Just (blk, bv) -> return $ AnyValue (LLVMPointerRepr (bvWidth bv)) $ LLVMPointer blk bv
  G.Float  -> AnyValue (FloatRepr SingleFloatRepr) <$> iFloatLit sym SingleFloatRepr 0
  G.Double -> AnyValue (FloatRepr DoubleFloatRepr) <$> iFloatLit sym DoubleFloatRepr 0
  G.Array n tp' ->
    do AnyValue tpr v <- unpackZero sym tp'
       return $ AnyValue (VectorRepr tpr) $ V.replicate (fromIntegral n) v
  G.Struct flds ->
    do xs <- traverse (unpackZero sym . view G.fieldVal) (V.toList flds)
       unpackStruct sym xs Ctx.empty Ctx.empty $ \ctx fls -> return $ AnyValue (StructRepr ctx) $ fls


-- | Unpack an 'LLVMVal' to produce a 'RegValue'.
unpackMemValue ::
  (HasCallStack, IsSymInterface sym) =>
  sym ->
  LLVMVal sym ->
  IO (AnyValue sym)

unpackMemValue sym (LLVMValZero tp) = unpackZero sym tp

-- If the block number is 0, we know this is a raw bitvector, and not an actual pointer.
unpackMemValue _sym (LLVMValInt blk bv)
  = return . AnyValue (LLVMPointerRepr (bvWidth bv)) $ LLVMPointer blk bv

unpackMemValue _ (LLVMValFloat sz x) =
  case sz of
    SingleSize ->
      return $ AnyValue (FloatRepr SingleFloatRepr) x
    DoubleSize ->
      return $ AnyValue (FloatRepr DoubleFloatRepr) x

unpackMemValue sym (LLVMValStruct xs) = do
  xs' <- traverse (unpackMemValue sym . snd) $ V.toList xs
  unpackStruct sym xs' Ctx.empty Ctx.empty $ \ctx fls -> return $ AnyValue (StructRepr ctx) $ fls
unpackMemValue sym (LLVMValArray tp xs) =
  asCrucibleType tp $ \tpr -> do
    xs' <- traverse (coerceAny sym tpr <=< unpackMemValue sym) xs
    return $ AnyValue (VectorRepr tpr) xs'

unpackStruct
   :: IsSymInterface sym
   => sym
   -> [AnyValue sym]
   -> CtxRepr ctx0
   -> Ctx.Assignment (RegValue' sym) ctx0
   -> (forall ctx. CtxRepr ctx -> Ctx.Assignment (RegValue' sym) ctx -> IO x)
   -> IO x
unpackStruct _ [] ctx fls k = k ctx fls
unpackStruct sym (v:vs) ctx fls k =
  case v of
    AnyValue tpr x ->
      unpackStruct sym vs (ctx Ctx.:> tpr) (fls Ctx.:> RV x) k


-- | Pack a 'RegValue' into an 'LLVMVal'. The LLVM storage type and
-- the Crucible type must be compatible.
packMemValue ::
  IsSymInterface sym =>
  sym ->
  G.Type      {- ^ LLVM storage type -} ->
  TypeRepr tp {- ^ Crucible type     -} ->
  RegValue sym tp ->
  IO (LLVMVal sym)

packMemValue _ (G.Type G.Float _) (FloatRepr SingleFloatRepr) x =
       return $ LLVMValFloat SingleSize x

packMemValue _ (G.Type G.Double _) (FloatRepr DoubleFloatRepr) x =
       return $ LLVMValFloat DoubleSize x

packMemValue sym (G.Type (G.Bitvector bytes) _) (BVRepr w) bv
  | bitsToBytes (natValue w) == bytes =
      do blk0 <- natLit sym 0
         return $ LLVMValInt blk0 bv

packMemValue _sym (G.Type (G.Bitvector bytes) _) (LLVMPointerRepr w) (LLVMPointer blk off)
  | bitsToBytes (natValue w) == bytes =
       return $ LLVMValInt blk off

packMemValue sym (G.Type (G.Array sz tp) _) (VectorRepr tpr) vec
  | V.length vec == fromIntegral sz = do
       vec' <- traverse (packMemValue sym tp tpr) vec
       return $ LLVMValArray tp vec'

packMemValue sym (G.Type (G.Struct fls) _) (StructRepr ctx) xs = do
  fls' <- V.generateM (V.length fls) $ \i -> do
              let fl = fls V.! i
              case Ctx.intIndex i (Ctx.size ctx) of
                Just (Some idx) -> do
                  let tpr = ctx Ctx.! idx
                  let RV val = xs Ctx.! idx
                  val' <- packMemValue sym (fl^.G.fieldVal) tpr val
                  return (fl, val')
                _ -> panic "MemModel.packMemValue"
                      [ "Mismatch between LLVM and Crucible types"
                      , "*** Filed out of bounds: " ++ show i
                      ]
  return $ LLVMValStruct fls'

packMemValue _ stTy crTy _ =
  panic "MemModel.packMemValue"
    [ "Type mismatch when storing value."
    , "*** Expected storable type: " ++ show stTy
    , "*** Given crucible type: " ++ show crTy
    ]

-- | Look up a 'Symbol' in the global map of the given 'MemImpl'.
-- Panic if the symbol is not present in the global map.
doResolveGlobal ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  L.Symbol {- ^ name of global -} ->
  IO (LLVMPtr sym wptr)
doResolveGlobal _sym mem symbol =
  case Map.lookup symbol (memImplGlobalMap mem) of
    Just (SomePointer ptr) | PtrWidth <- ptrWidth ptr -> return ptr
    _ -> panic "MemModel.doResolveGlobal"
            [ "Unable to resolve global symbol."
            , "*** Name: " ++ show symbol
            ]

ppMem :: IsExprBuilder sym => MemImpl sym -> Doc
ppMem mem = G.ppMem (memImplHeap mem)

-- | Pretty print a memory state to the given handle.
doDumpMem :: IsExprBuilder sym => Handle -> MemImpl sym -> IO ()
doDumpMem h mem = do
  hPutStrLn h (show (ppMem mem))

-- | Load an LLVM value from memory. Also assert that the pointer is
-- valid and the result value is not undefined.
loadRaw :: (IsSymInterface sym, HasPtrWidth wptr)
        => sym
        -> MemImpl sym
        -> LLVMPtr sym wptr
        -> G.Type
        -> IO (LLVMVal sym)
loadRaw sym mem ptr valType =
  do res <- loadRawWithCondition sym mem ptr valType
     case res of
       Right (p,r,v) -> v <$ assert sym p r
       Left e        -> addFailedAssertion sym (AssertFailureSimError e)


-- | Load an LLVM value from memory. This version of 'loadRaw'
-- returns the side-conditions explicitly so that they can
-- be conditionally asserted.
loadRawWithCondition ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym                  ->
  MemImpl sym          {- ^ LLVM heap       -} ->
  LLVMPtr sym wptr     {- ^ pointer         -} ->
  G.Type               {- ^ pointed-to type -} ->
  IO (Either
        String
        (Pred sym, SimErrorReason, LLVMVal sym))
  -- ^ Either error message or
  -- (assertion, assertion failure description, dereferenced value)
loadRawWithCondition sym mem ptr valType =
  do v <- G.readMem sym PtrWidth ptr valType 0 (memImplHeap mem)
     let errMsg = "Invalid memory load: address " ++ show (G.ppPtr ptr) ++
                  " at type "                     ++ show (G.ppType valType)
     case v of
       Unassigned -> return (Left errMsg)
       PE p' v' -> return (Right (p', AssertFailureSimError errMsg, v'))

-- | Load a 'RegValue' from memory. Also assert that the pointer is
-- valid and aligned, and that the loaded value is defined.
doLoad ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ pointer to load from      -} ->
  G.Type           {- ^ type of value to load     -} ->
  Alignment        {- ^ assumed pointer alignment -} ->
  IO (RegValue sym AnyType)
doLoad sym mem ptr valType alignment = do
    --putStrLn "MEM LOAD"
    let errMsg = "Invalid memory load: address " ++ show (G.ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    v <- G.readMem sym PtrWidth ptr valType alignment (memImplHeap mem)
    case v of
      Unassigned -> addFailedAssertion sym (AssertFailureSimError errMsg)
      PE p' v' -> do
        assert sym p' (AssertFailureSimError errMsg)
        unpackMemValue sym v'

-- | Store an LLVM value in memory. Also assert that the pointer is
-- valid and points to a mutable memory region.
storeRaw :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr {- ^ pointer to store into -}
  -> G.Type           {- ^ type of value to store -}
  -> LLVMVal sym      {- ^ value to store -}
  -> IO (MemImpl sym)
storeRaw sym mem ptr valType val = do
    (p, heap') <- G.writeMem sym PtrWidth ptr valType val (memImplHeap mem)
    let errMsg = "Invalid memory store: address " ++ show (G.ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    assert sym p (AssertFailureSimError errMsg)
    return mem{ memImplHeap = heap' }

-- | Store an LLVM value in memory. The pointed-to memory region may
-- be either mutable or immutable; thus 'storeConstRaw' can be used to
-- initialize read-only memory regions.
storeConstRaw :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr {- ^ pointer to store into -}
  -> G.Type           {- ^ type of value to store -}
  -> LLVMVal sym      {- ^ value to store -}
  -> IO (MemImpl sym)
storeConstRaw sym mem ptr valType val = do
    (p, heap') <- G.writeConstMem sym PtrWidth ptr valType val (memImplHeap mem)
    let errMsg = "Invalid memory store: address " ++ show (G.ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    assert sym p (AssertFailureSimError errMsg)
    return mem{ memImplHeap = heap' }

-- | Store a 'RegValue' in memory. Also assert that the pointer is
-- valid and points to a mutable memory region.
doStore ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ pointer to store into  -} ->
  TypeRepr tp ->
  G.Type           {- ^ type of value to store -} ->
  RegValue sym tp  {- ^ value to store         -} ->
  IO (MemImpl sym)
doStore sym mem ptr tpr valType val = do
    --putStrLn "MEM STORE"
    val' <- packMemValue sym valType tpr val
    storeRaw sym mem ptr valType val'

data SomeFnHandle where
  SomeFnHandle :: FnHandle args ret -> SomeFnHandle


sextendBVTo :: (1 <= w, IsSymInterface sym)
            => sym
            -> NatRepr w
            -> NatRepr w'
            -> SymExpr sym (BaseBVType w)
            -> IO (SymExpr sym (BaseBVType w'))
sextendBVTo sym w w' x
  | Just Refl <- testEquality w w' = return x
  | Just LeqProof <- testLeq (incNat w) w' = bvSext sym w' x
  | otherwise =
    addFailedAssertion sym
        $ AssertFailureSimError
        $ unwords ["cannot extend bitvector of width", show (natValue w)
                                                     , "to", show (natValue w') ]

-- | Assert that two memory regions are disjoint.
-- Two memory regions are disjoint if any of the following are true:
--
--   1. Their block pointers are different
--   2. Their blocks are the same, but /dest+dlen/ <= /src/
--   3. Their blocks are the same, but /src+slen/ <= /dest/
assertDisjointRegions' ::
  (1 <= w, HasPtrWidth wptr, IsSymInterface sym) =>
  String {- ^ label used for error message -} ->
  sym ->
  NatRepr w ->
  LLVMPtr sym wptr {- ^ pointer to region 1 -} ->
  SymBV sym w      {- ^ length of region 1  -} ->
  LLVMPtr sym wptr {- ^ pointer to region 2 -} ->
  SymBV sym w      {- ^ length of region 2  -} ->
  IO ()
assertDisjointRegions' lbl sym w dest dlen src slen = do
  c <- buildDisjointRegionsAssertion sym w dest dlen src slen
  assert sym c
     (AssertFailureSimError ("Memory regions not disjoint in " ++ lbl))


buildDisjointRegionsAssertion ::
  (1 <= w, HasPtrWidth wptr, IsSymInterface sym) =>
  sym ->
  NatRepr w ->
  LLVMPtr sym wptr {- ^ pointer to region 1 -} ->
  SymBV sym w      {- ^ length of region 1  -} ->
  LLVMPtr sym wptr {- ^ pointer to region 2 -} ->
  SymBV sym w      {- ^ length of region 2  -} ->
  IO (Pred sym)
buildDisjointRegionsAssertion sym w dest dlen src slen = do
  let LLVMPointer dblk doff = dest
  let LLVMPointer sblk soff = src

  dend <- bvAdd sym doff =<< sextendBVTo sym w PtrWidth dlen
  send <- bvAdd sym soff =<< sextendBVTo sym w PtrWidth slen

  diffBlk   <- notPred sym =<< natEq sym dblk sblk
  destfirst <- bvSle sym dend soff
  srcfirst  <- bvSle sym send doff

  orPred sym diffBlk =<< orPred sym destfirst srcfirst


-- | Simpler interface to 'assertDisjointRegions'' where the lengths
-- of the two regions are equal as used by the @memcpy@ operation.
assertDisjointRegions ::
  (1 <= w, HasPtrWidth wptr, IsSymInterface sym) =>
  sym ->
  NatRepr w ->
  LLVMPtr sym wptr {- ^ pointer to region 1       -} ->
  LLVMPtr sym wptr {- ^ pointer to region 2       -} ->
  SymBV sym w      {- ^ length of regions 1 and 2 -} ->
  IO ()
assertDisjointRegions sym w dest src len =
  assertDisjointRegions' "memcpy" sym w dest len src len


-- | Allocate and zero a memory region with /size * number/ bytes.
-- Also assert that the multiplication does not overflow.
doCalloc ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  SymBV sym wptr {- ^ size   -} ->
  SymBV sym wptr {- ^ number -} ->
  IO (LLVMPtr sym wptr, MemImpl sym)
doCalloc sym mem sz num = do
  (ov, sz') <- unsignedWideMultiplyBV sym sz num
  ov_iszero <- notPred sym =<< bvIsNonzero sym ov
  assert sym ov_iszero
     (AssertFailureSimError "Multiplication overflow in calloc()")

  z <- bvLit sym knownNat 0
  (ptr, mem') <- doMalloc sym G.HeapAlloc G.Mutable "<calloc>" mem sz'
  mem'' <- doMemset sym PtrWidth mem' ptr z sz'
  return (ptr, mem'')

-- | Allocate a memory region.
doMalloc
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> G.AllocType {- ^ stack, heap, or global -}
  -> G.Mutability {- ^ whether region is read-only -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> SymBV sym wptr {- ^ allocation size -}
  -> IO (LLVMPtr sym wptr, MemImpl sym)
doMalloc sym allocType mut loc mem sz = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- natLit sym (fromIntegral blkNum)
  z <- bvLit sym PtrWidth 0
  let heap' = G.allocMem allocType (fromInteger blkNum) sz mut loc (memImplHeap mem)
  let ptr = LLVMPointer blk z
  return (ptr, mem{ memImplHeap = heap' })

-- | Allocate a memory region on the heap, with no source location info.
mallocRaw
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> SymBV sym wptr {- ^ size in bytes -}
  -> IO (LLVMPtr sym wptr, MemImpl sym)
mallocRaw sym mem sz =
  doMalloc sym G.HeapAlloc G.Mutable "<malloc>" mem sz

-- | Allocate a read-only memory region on the heap, with no source location info.
mallocConstRaw
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> SymBV sym wptr
  -> IO (LLVMPtr sym wptr, MemImpl sym)
mallocConstRaw sym mem sz =
  doMalloc sym G.HeapAlloc G.Immutable "<malloc>" mem sz

-- | Allocate a memory region for the given handle.
doMallocHandle
  :: (Typeable a, IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> G.AllocType {- ^ stack, heap, or global -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> a {- ^ handle -}
  -> IO (LLVMPtr sym wptr, MemImpl sym)
doMallocHandle sym allocType loc mem x = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- natLit sym (fromIntegral blkNum)
  z <- bvLit sym PtrWidth 0

  let heap' = G.allocMem allocType (fromInteger blkNum) z G.Immutable loc (memImplHeap mem)
  let hMap' = Map.insert blkNum (toDyn x) (memImplHandleMap mem)
  let ptr = LLVMPointer blk z
  return (ptr, mem{ memImplHeap = heap', memImplHandleMap = hMap' })

-- | Look up the handle associated with the given pointer, if any.
doLookupHandle
  :: (Typeable a, IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr
  -> IO (Either Doc a)
doLookupHandle _sym mem ptr = do
  let LLVMPointer blk _ = ptr
  case asNat blk of
    Nothing -> return (Left (text "Cannot resolve a symbolic pointer to a function handle:" <$$> ppPtr ptr))
    Just i
      | i == 0 -> return (Left (text "Cannot treat raw bitvector as function pointer:" <$$> ppPtr ptr))
      | otherwise ->
          case Map.lookup (toInteger i) (memImplHandleMap mem) of
            Nothing -> return (Left ("Pointer is not a function pointer:" <$$> ppPtr ptr))
            Just x ->
              case fromDynamic x of
                Nothing -> return (Left ("Function handle did not have expected type:" <$$> ppPtr ptr))
                Just a  -> return (Right a)

-- | Free the memory region pointed to by the given pointer. Also
-- assert that the pointer either points to the beginning of an
-- allocated region, or is null. Freeing a null pointer has no effect.
doFree
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr
  -> IO (MemImpl sym)
doFree sym mem ptr = do
  let LLVMPointer blk _ = ptr
  (c, heap') <- G.freeMem sym PtrWidth ptr (memImplHeap mem)

  -- If this pointer is a handle pointer, remove the associated data
  let hMap' =
       case asNat blk of
         Just i  -> Map.delete (toInteger i) (memImplHandleMap mem)
         Nothing -> memImplHandleMap mem

  let errMsg = "Invalid free (double free or invalid pointer): address " ++ show (G.ppPtr ptr)

  -- NB: free is defined and has no effect if passed a null pointer
  isNull <- ptrIsNull sym PtrWidth ptr
  c' <- orPred sym c isNull
  assert sym c' (AssertFailureSimError errMsg)
  return mem{ memImplHeap = heap', memImplHandleMap = hMap' }

-- | Fill a memory range with copies of the specified byte. Also
-- assert that the memory range falls within a valid allocated region.
doMemset ::
  (1 <= w, IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  NatRepr w ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ destination -} ->
  SymBV sym 8      {- ^ fill byte   -} ->
  SymBV sym w      {- ^ length      -} ->
  IO (MemImpl sym)
doMemset sym w mem dest val len = do
  len' <- sextendBVTo sym w PtrWidth len

  (c, heap') <- G.setMem sym PtrWidth dest val len' (memImplHeap mem)

  assert sym c
     (AssertFailureSimError "Invalid memory region in memset")

  return mem{ memImplHeap = heap' }

-- | Copy memory from source to destination. Also assert that the
-- source and destination pointers fall within valid allocated
-- regions.
doMemcpy ::
  (1 <= w, IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  NatRepr w ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ destination -} ->
  LLVMPtr sym wptr {- ^ source      -} ->
  SymBV sym w      {- ^ length      -} ->
  IO (MemImpl sym)
doMemcpy sym w mem dest src len = do
  len' <- sextendBVTo sym w PtrWidth len

  (c, heap') <- G.copyMem sym PtrWidth dest src len' (memImplHeap mem)

  assert sym c
     (AssertFailureSimError "Invalid memory region in memcpy")

  return mem{ memImplHeap = heap' }


doPtrSubtract ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  LLVMPtr sym wptr ->
  LLVMPtr sym wptr ->
  IO (SymBV sym wptr)
doPtrSubtract sym _m x y =
  do ptrDiff sym PtrWidth x y

-- | Add an offset to a pointer. Also assert that the result is a valid pointer.
doPtrAddOffset ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ base pointer -} ->
  SymBV sym wptr   {- ^ offset       -} ->
  IO (LLVMPtr sym wptr)
doPtrAddOffset sym m x off = do
   x' <- ptrAdd sym PtrWidth x off
   v  <- isValidPointer sym x' m
   let x_doc = G.ppPtr x
   let off_doc = printSymExpr off
   assert sym v
       (AssertFailureSimError $ unlines ["Pointer arithmetic resulted in invalid pointer:", show x_doc, show off_doc])
   return x'

-- | This predicate tests if the pointer is a valid, live pointer
--   into the heap, OR is the distinguished NULL pointer.
isValidPointer ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  LLVMPtr sym wptr ->
  MemImpl sym ->
  IO (Pred sym)
isValidPointer sym p mem =
   do np <- ptrIsNull sym PtrWidth p
      case asConstantPred np of
        Just True  -> return np
        Just False -> G.isValidPointer sym PtrWidth p (memImplHeap mem)
        _ -> orPred sym np =<< G.isValidPointer sym PtrWidth p (memImplHeap mem)

-- | Load a null-terminated string from the memory.
--
-- The pointer to read from must be concrete and nonnull.  Moreover,
-- we require all the characters in the string to be concrete.
-- Otherwise it is very difficult to tell when the string has
-- terminated.  If a maximum number of characters is provided, no more
-- than that number of charcters will be read.  In either case,
-- `loadString` will stop reading if it encounters a null-terminator.
loadString ::
  forall sym wptr.
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym      {- ^ memory to read from        -} ->
  LLVMPtr sym wptr {- ^ pointer to string value    -} ->
  Maybe Int        {- ^ maximum characters to read -} ->
  IO [Word8]
loadString sym mem = go id
 where
  go :: ([Word8] -> [Word8]) -> LLVMPtr sym wptr -> Maybe Int -> IO [Word8]
  go f _ (Just 0) = return $ f []
  go f p maxChars = do
     v <- doLoad sym mem p (G.bitvectorType 1) 0 -- one byte, no alignment
     case v of
       AnyValue (LLVMPointerRepr w) x
         | Just Refl <- testEquality w (knownNat :: NatRepr 8) ->
            do x' <- projectLLVM_bv sym x
               case asUnsignedBV x' of
                 Just 0 -> return $ f []
                 Just c -> do
                     let c' :: Word8 = toEnum $ fromInteger c
                     p' <- doPtrAddOffset sym mem p =<< bvLit sym PtrWidth 1
                     go (f . (c':)) p' (fmap (\n -> n - 1) maxChars)
                 Nothing ->
                   addFailedAssertion sym
                      $ Unsupported "Symbolic value encountered when loading a string"
       _ -> panic "MemModel.loadString"
              [ "Invalid value encountered when loading a string" ]


-- | Like 'loadString', except the pointer to load may be null.  If
--   the pointer is null, we return Nothing.  Otherwise we load
--   the string as with 'loadString' and return it.
loadMaybeString ::
  forall sym wptr.
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym      {- ^ memory to read from        -} ->
  LLVMPtr sym wptr {- ^ pointer to string value    -} ->
  Maybe Int        {- ^ maximum characters to read -} ->
  IO (Maybe [Word8])
loadMaybeString sym mem ptr n = do
  isnull <- ptrIsNull sym PtrWidth ptr
  case asConstantPred isnull of
    Nothing    -> addFailedAssertion sym
                    $ Unsupported "Symbolic pointer encountered when loading a string"
    Just True  -> return Nothing
    Just False -> Just <$> loadString sym mem ptr n



toStorableType :: (Monad m, HasPtrWidth wptr)
               => MemType
               -> m G.Type
toStorableType mt =
  case mt of
    IntType n -> return $ G.bitvectorType (bitsToBytes n)
    PtrType _ -> return $ G.bitvectorType (bitsToBytes (natValue PtrWidth))
    FloatType -> return $ G.floatType
    DoubleType -> return $ G.doubleType
    ArrayType n x -> G.arrayType (fromIntegral n) <$> toStorableType x
    VecType n x -> G.arrayType (fromIntegral n) <$> toStorableType x
    MetadataType -> fail "toStorableType: Cannot store metadata values"
    StructType si -> G.mkStructType <$> traverse transField (siFields si)
      where transField :: Monad m => FieldInfo -> m (G.Type, Bytes)
            transField fi = do
               t <- toStorableType $ fiType fi
               return (t, fiPadding fi)

----------------------------------------------------------------------
-- constToLLVMVal
--

-- | This is used (by saw-script) to initialize globals.
--
-- In this translation, we lose the distinction between pointers and ints.
--
constToLLVMVal :: forall wptr sym.
  ( HasPtrWidth wptr
  , IsSymInterface sym
  ) => sym               -- ^ The symbolic backend
    -> MemImpl sym       -- ^ The current memory state, for looking up globals
    -> LLVMConst         -- ^ Constant expression to translate
    -> IO (LLVMVal sym)  -- ^ Runtime representation of the constant expression

-- See comment on @LLVMVal@ on why we use a literal 0.
constToLLVMVal sym _ (IntConst w i) =
  LLVMValInt <$> natLit sym 0 <*> (bvLit sym w i)

constToLLVMVal sym _ (FloatConst f) =
  LLVMValFloat SingleSize <$> iFloatLitSingle sym f

constToLLVMVal sym _ (DoubleConst d) =
  LLVMValFloat DoubleSize <$> iFloatLitDouble sym d

constToLLVMVal sym mem (ArrayConst memty xs) =
  LLVMValArray <$> toStorableType memty
               <*> (V.fromList <$> traverse (constToLLVMVal sym mem) xs)

-- Same as the array case
constToLLVMVal sym mem (VectorConst memty xs) =
  LLVMValArray <$> toStorableType memty
               <*> (V.fromList <$> traverse (constToLLVMVal sym mem) xs)

constToLLVMVal sym mem (StructConst sInfo xs) =
  LLVMValStruct <$>
    V.zipWithM (\x y -> (,) <$> fiToFT x <*> constToLLVMVal sym mem y)
               (siFields sInfo)
               (V.fromList xs)

-- SymbolConsts are offsets from global pointers. We translate them into the
-- pointer they represent.
constToLLVMVal sym mem (SymbolConst symb i) = do
  ptr <- doResolveGlobal sym mem symb     -- Pointer to the global "symb"
  ibv <- bvLit sym ?ptrWidth i         -- Offset to be added, as a bitvector

  -- blk is the allocation number that this global is stored in.
  -- In contrast to the case for @IntConst@ above, it is non-zero.
  let (blk, offset) = llvmPointerView ptr
  LLVMValInt blk <$> bvAdd sym offset ibv

constToLLVMVal _sym _mem (ZeroConst memty) = LLVMValZero <$> toStorableType memty


-- TODO are these types just identical? Maybe we should combine them.
fiToFT :: (HasPtrWidth wptr, Monad m) => FieldInfo -> m (G.Field G.Type)
fiToFT fi = fmap (\t -> G.mkField (fiOffset fi) t (fiPadding fi))
                 (toStorableType $ fiType fi)
