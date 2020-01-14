{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}

-- | A parser for an s-expression representation of what4 expressions
module What4.Serialize.Parser
  ( readSymFn
  , readSymFnFromFile
  , readSymFnEnv
  , readSymFnEnvFromFile
  , ParserConfig(..)
  , defaultParserConfig
  , SymFnEnv
  ) where

import qualified Control.Monad.Except as E
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Control.Monad.Reader as MR
import           Data.Kind
import           Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.SCargot.Repr.WellFormed as S

import           Data.Semigroup
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Text.Printf ( printf )

import qualified Data.Parameterized.Ctx as Ctx
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import qualified Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.TraversableFC ( traverseFC, allFC )
import           What4.BaseTypes

import qualified What4.Interface as W4

import           What4.Serialize.SETokens ( Atom(..), printSExpr, parseSExpr)
import qualified What4.Utils.Log as U
import           What4.Utils.Util ( SomeSome(..) )
import qualified What4.Utils.Util as U

import           Prelude


type SExp = S.WellFormedSExpr Atom

-- * First pass of parsing turns the raw text into s-expressions.
--   This pass is handled by the code in What4.Serialize.SETokens

-- * Second pass of parsing: turning the s-expressions into symbolic expressions
-- and the overall templated formula

-- ** Utility functions

-- | Utility function for contextualizing errors. Prepends the given prefix
-- whenever an error is thrown.
prefixError :: (Monoid e, E.MonadError e m) => e -> m a -> m a
prefixError prefix act = E.catchError act (E.throwError . mappend prefix)

-- | Utility function for lifting a 'Maybe' into a 'MonadError'
fromMaybeError :: (E.MonadError e m) => e -> Maybe a -> m a
fromMaybeError err = maybe (E.throwError err) return


data ParsedVariable sym (tps :: Ctx.Ctx BaseType) (tp :: BaseType) where
  ParsedArgument :: BaseTypeRepr tp -> Ctx.Index tps tp
                 -> ParsedVariable sym tps tp
  ParsedGlobal :: W4.SymExpr sym tp -> ParsedVariable sym tps tp

-- | Data about the argument pertinent after parsing: their name and their type.
data ArgData (tp :: BaseType) where
  ArgData :: String -> BaseTypeRepr tp -> ArgData tp


readBaseType :: forall m
              . (E.MonadError String m)
             => SExp
             -> m (Some BaseTypeRepr)
readBaseType sexpr =
  case sexpr of
    S.WFSAtom (AIdent atom) ->
      case atom of
        "Bool" -> return $ Some BaseBoolRepr
        "Nat" -> return $ Some BaseNatRepr
        "Int" -> return $ Some BaseIntegerRepr
        "Real" -> return $ Some BaseRealRepr
        "String" -> return $ Some (BaseStringRepr UnicodeRepr)
        "Complex" -> return $ Some BaseComplexRepr
        _ -> panic
    S.WFSList [(S.WFSAtom (AIdent "BV")), (S.WFSAtom (AInt w))]
      | Just (Some wRepr) <- someNat w
      , Just LeqProof <- testLeq (knownNat @1) wRepr
        -> return $ Some (BaseBVRepr wRepr)
      | otherwise
        -> panic
    S.WFSList [(S.WFSAtom (AIdent "Struct")), args] -> do
      Some tps <- readBaseTypes args
      return $ Some (BaseStructRepr tps)
    S.WFSList [S.WFSAtom (AIdent "Array"), ixArgs, tpArg] -> do
      Some ixs <- readBaseTypes ixArgs
      Some tp <- readBaseType tpArg
      case Ctx.viewAssign ixs of
        Ctx.AssignEmpty -> E.throwError $ "array type has no indices: " ++ show sexpr
        Ctx.AssignExtend _ _ -> return $ Some (BaseArrayRepr ixs tp)
    _ -> panic
  where
    panic = E.throwError $ "unknown base type: " ++ show sexpr

readBaseTypes :: forall m
              . (E.MonadError String m)
              => SExp
              -> m (Some (Ctx.Assignment BaseTypeRepr))
readBaseTypes sexpr@(S.WFSAtom _) = E.throwError $ "expected list of base types: " ++ show sexpr
readBaseTypes (S.WFSList sexprs) =
  go sexprs
  where
    go :: [SExp] -> m (Some (Ctx.Assignment BaseTypeRepr))
    go sexpr =
      case sexpr of
        [] -> return (Some Ctx.empty)
        (s:rest) -> do
          Some tp <- readBaseType s
          Some tps <- go rest
          return $ Some $ Ctx.extend tps tp

-- | Short-lived type that just stores an index with its corresponding type
-- representation, with the type parameter ensuring they correspond to one another.
data IndexWithType (sh :: Ctx.Ctx BaseType) (tp :: BaseType) where
  IndexWithType :: BaseTypeRepr tp -> Ctx.Index sh tp -> IndexWithType sh tp

-- | Look up a name in the given operand list, returning its index and type if found.
findArgListIndex :: forall sh. String -> Ctx.Assignment ArgData sh -> Maybe (Some (IndexWithType sh))
findArgListIndex x args = Ctx.forIndex (Ctx.size args) getArg Nothing
  where
    getArg :: forall tp
            . Maybe (Some (IndexWithType sh))
           -> Ctx.Index sh tp
           -> Maybe (Some (IndexWithType sh))
    getArg Nothing idx = case args Ctx.! idx of
      ArgData name tpRepr
        | name == x -> Just $ Some (IndexWithType tpRepr idx)
      _ -> Nothing
    getArg (Just iwt) _ = Just iwt


-- | Parse a single parameter, given the list of operands to use as a lookup.
readVariable :: forall sym tps m. (E.MonadError String m) => (String -> (Maybe (Some (W4.SymExpr sym)))) -> Ctx.Assignment ArgData tps -> String -> m (Some (ParsedVariable sym tps))
readVariable lookupGlobal arglist name = do
  case lookupGlobal name of
    Just (Some glb) -> return $ Some (ParsedGlobal glb)
    Nothing
      | Just (Some (IndexWithType tpRepr idx)) <- findArgListIndex name arglist ->
        return $ Some (ParsedArgument tpRepr idx)
    _ -> E.throwError $ printf "couldn't find binding for variable %s" name

-- ** Parsing definitions

-- | "Global" data stored in the Reader monad throughout parsing the definitions.
data DefsInfo sym tps =
  DefsInfo
  { getSym :: sym
    -- ^ SymInterface/ExprBuilder used to build up symbolic
    -- expressions while parsing the definitions.
    , getFnEnv :: SymFnEnv sym
    -- ^ Global SymFn environment.
    , getBaseEnv :: (BaseEnv sym)
    -- ^ Function to retrieve the expression corresponding to the
    -- given global variable (which is not a SymFn).
    , getArgVarList :: Ctx.Assignment (W4.BoundVar sym) tps
    -- ^ ShapedList used to retrieve the variable
    -- corresponding to a given argument.
    , getArgNameList :: Ctx.Assignment ArgData tps
    -- ^ ShapedList used to look up the index given an
    -- argument's name.
    , getLetBindings :: BaseEnv sym
    -- ^ Mapping of currently in-scope let-bound variables
    --- to their parsed bindings.
    }

-- | Stores a NatRepr along with proof that its type parameter is a bitvector of
-- that length. Used for easy pattern matching on the LHS of a binding in a
-- do-expression to extract the proof.
data BVProof tp where
  BVProof :: forall n. (1 <= n) => NatRepr n -> BVProof (BaseBVType n)

-- | Given an expression, monadically either returns proof that it is a
-- bitvector or throws an error.
getBVProof :: (W4.IsExpr ex, E.MonadError String m) => ex tp -> m (BVProof tp)
getBVProof expr =
  case W4.exprType expr of
    BaseBVRepr n -> return $ BVProof n
    t -> E.throwError $ printf "expected BV, found %s" (show t)


-- | Operator type descriptions for parsing s-expression of
-- the form @(operator operands ...)@.
data Op sym where
  -- | Generic unary operator description.
    Op1 :: Ctx.Assignment BaseTypeRepr (Ctx.EmptyCtx Ctx.::> arg1)
        -> (sym ->
            W4.SymExpr sym arg1 ->
            IO (W4.SymExpr sym ret))
        -> Op sym
  -- | Generic dyadic operator description.
    Op2 :: Ctx.Assignment BaseTypeRepr (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2)
        -> (sym ->
            W4.SymExpr sym arg1 ->
            W4.SymExpr sym arg2 ->
            IO (W4.SymExpr sym ret))
        -> Op sym
  -- | Generic triadic operator description.
    Op3 :: Ctx.Assignment BaseTypeRepr (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2 Ctx.::> arg3)
        -> (sym ->
            W4.SymExpr sym arg1 ->
            W4.SymExpr sym arg2 ->
            W4.SymExpr sym arg3 ->
            IO (W4.SymExpr sym ret)
           )
        -> Op sym
    -- | Generic tetradic operator description.
    Op4 :: Ctx.Assignment
           BaseTypeRepr
           (Ctx.EmptyCtx Ctx.::> arg1 Ctx.::> arg2 Ctx.::> arg3 Ctx.::> arg4)
        -> ( sym ->
             W4.SymExpr sym arg1 ->
             W4.SymExpr sym arg2 ->
             W4.SymExpr sym arg3 ->
             W4.SymExpr sym arg4 ->
             IO (W4.SymExpr sym ret)
           )
        -> Op sym
    -- | Encapsulating type for a unary operation that takes one bitvector and
    -- returns another (in IO).
    BVOp1 :: (forall w . (1 <= w) =>
               sym ->
               W4.SymBV sym w ->
               IO (W4.SymBV sym w))
          -> Op sym
    -- | Binop with a bitvector return type, e.g., addition or bitwise operations.
    BVOp2 :: (forall w . (1 <= w) =>
               sym ->
               W4.SymBV sym w ->
               W4.SymBV sym w ->
               IO (W4.SymBV sym w))
          -> Op sym
    -- | Bitvector binop with a boolean return type, i.e., comparison operators.
    BVComp2 :: (forall w . (1 <= w) =>
                    sym ->
                    W4.SymBV sym w ->
                    W4.SymBV sym w ->
                    IO (W4.Pred sym))
                -> Op sym

-- | Lookup mapping operators to their Op definitions (if they exist)
lookupOp :: forall sym . W4.IsSymExprBuilder sym => String -> Maybe (Op sym)
lookupOp = \case
  -- -- -- Boolean ops -- -- --
  "andp" -> Just $ Op2 knownRepr $ W4.andPred
  "orp"  -> Just $ Op2 knownRepr $ W4.orPred
  "xorp" -> Just $ Op2 knownRepr $ W4.xorPred
  "notp" -> Just $ Op1 knownRepr $ W4.notPred
  -- -- -- Natural ops -- -- --
  "natmul" -> Just $ Op2 knownRepr $ W4.natMul
  "natadd" -> Just $ Op2 knownRepr $ W4.natAdd
  "natle"  -> Just $ Op2 knownRepr $ W4.natLe
  -- -- -- Integer ops -- -- --
  "intmul" -> Just $ Op2 knownRepr $ W4.intMul
  "intadd" -> Just $ Op2 knownRepr $ W4.intAdd
  "intmod" -> Just $ Op2 knownRepr $ W4.intMod
  "intdiv" -> Just $ Op2 knownRepr $ W4.intDiv
  "intle"  -> Just $ Op2 knownRepr $ W4.intLe
  "intabs" -> Just $ Op1 knownRepr $ W4.intAbs
  -- -- -- Bitvector ops -- -- --
  "bvand" -> Just $ BVOp2 W4.bvAndBits
  "bvor" -> Just $ BVOp2 W4.bvOrBits
  "bvadd" -> Just $ BVOp2 W4.bvAdd
  "bvmul" -> Just $ BVOp2 W4.bvMul
  "bvudiv" -> Just $ BVOp2 W4.bvUdiv
  "bvurem" -> Just $ BVOp2 W4.bvUrem
  "bvshl" -> Just $ BVOp2 W4.bvShl
  "bvlshr" -> Just $ BVOp2 W4.bvLshr
  "bvnand" -> Just $ BVOp2 $ \sym arg1 arg2 -> W4.bvNotBits sym =<< W4.bvAndBits sym arg1 arg2
  "bvnor" -> Just $ BVOp2 $ \sym arg1 arg2 -> W4.bvNotBits sym =<< W4.bvOrBits sym arg1 arg2
  "bvxor" -> Just $ BVOp2 W4.bvXorBits
  "bvxnor" -> Just $ BVOp2 $ \sym arg1 arg2 -> W4.bvNotBits sym =<< W4.bvXorBits sym arg1 arg2
  "bvsub" -> Just $ BVOp2 W4.bvSub
  "bvsdiv" -> Just $ BVOp2 W4.bvSdiv
  "bvsrem" -> Just $ BVOp2 W4.bvSrem
  "bvsmod" -> error "bvsmod is not implemented"
  "bvashr" -> Just $ BVOp2 W4.bvAshr
  "bvult" -> Just $ BVComp2 W4.bvUlt
  "bvule" -> Just $ BVComp2 W4.bvUle
  "bvugt" -> Just $ BVComp2 W4.bvUgt
  "bvuge" -> Just $ BVComp2 W4.bvUge
  "bvslt" -> Just $ BVComp2 W4.bvSlt
  "bvsle" -> Just $ BVComp2 W4.bvSle
  "bvsgt" -> Just $ BVComp2 W4.bvSgt
  "bvsge" -> Just $ BVComp2 W4.bvSge
  "bveq" -> Just $ BVComp2 W4.bvEq
  "bvne" -> Just $ BVComp2 W4.bvNe
  "bvneg" -> Just $ BVOp1 W4.bvNeg
  "bvnot" -> Just $ BVOp1 W4.bvNotBits
  -- -- -- Floating point ops -- -- --
  "fnegd" -> Just $ Op1 knownRepr $ W4.floatNeg @_ @Prec64
  "fnegs" -> Just $ Op1 knownRepr $ W4.floatNeg @_ @Prec32
  "fabsd" -> Just $ Op1 knownRepr $ W4.floatAbs @_ @Prec64
  "fabss" -> Just $ Op1 knownRepr $ W4.floatAbs @_ @Prec32
  "fsqrt" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatSqrt @_ @Prec64 sym rm x
  "fsqrts" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatSqrt @_ @Prec32 sym rm x
  "fnand" -> Just $ Op1 knownRepr $ W4.floatIsNaN @_ @Prec64
  "fnans" -> Just $ Op1 knownRepr $ W4.floatIsNaN @_ @Prec32
  "frsp" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatCast @_ @Prec32 @Prec64 sym knownRepr rm x
  "fp_single_to_double" -> Just $ Op1 knownRepr $ \sym ->
    W4.floatCast @_ @Prec64 @Prec32 sym knownRepr W4.RNE
  "fp_binary_to_double" ->
    Just $ Op1 knownRepr $ \sym -> W4.floatFromBinary @_ @11 @53 sym knownRepr
  "fp_binary_to_single" ->
    Just $ Op1 knownRepr $ \sym -> W4.floatFromBinary @_ @8 @24 sym knownRepr
  "fp_double_to_binary" -> Just $ Op1 knownRepr $ W4.floatToBinary @_ @11 @53
  "fp_single_to_binary" -> Just $ Op1 knownRepr $ W4.floatToBinary @_ @8 @24
  "fctid" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatToSBV @_ @64 @Prec64 sym knownRepr rm x
  "fctidu" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatToBV @_ @64 @Prec64 sym knownRepr rm x
  "fctiw" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatToSBV @_ @32 @Prec64 sym knownRepr rm x
  "fctiwu" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatToBV @_ @32 @Prec64 sym knownRepr rm x
  "fcfid" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.sbvToFloat @_ @64 @Prec64 sym knownRepr rm x
  "fcfids" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.sbvToFloat @_ @64 @Prec32 sym knownRepr rm x
  "fcfidu" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.bvToFloat @_ @64 @Prec64 sym knownRepr rm x
  "fcfidus" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.bvToFloat @_ @64 @Prec32 sym knownRepr rm x
  "frti" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatRound @_ @Prec64 sym rm x
  "frtis" -> Just $ Op2 knownRepr $ \sym r x -> U.withRounding sym r $ \rm ->
    W4.floatRound @_ @Prec32 sym rm x
  "fadd" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatAdd @_ @Prec64 sym rm x y
  "fadds" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatAdd @_ @Prec32 sym rm x y
  "fsub" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatSub @_ @Prec64 sym rm x y
  "fsubs" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatSub @_ @Prec32 sym rm x y
  "fmul" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatMul @_ @Prec64 sym rm x y
  "fmuls" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatMul @_ @Prec32 sym rm x y
  "fdiv" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatDiv @_ @Prec64 sym rm x y
  "fdivs" -> Just $ Op3 knownRepr $ \sym r x y -> U.withRounding sym r $ \rm ->
    W4.floatDiv @_ @Prec32 sym rm x y
  "fltd" -> Just $ Op2 knownRepr $ W4.floatLt @_ @Prec64
  "flts" -> Just $ Op2 knownRepr $ W4.floatLt @_ @Prec32
  "feqd" -> Just $ Op2 knownRepr $ W4.floatFpEq @_ @Prec64
  "feqs" -> Just $ Op2 knownRepr $ W4.floatFpEq @_ @Prec32
  "fled" -> Just $ Op2 knownRepr $ W4.floatLe @_ @Prec64
  "fles" -> Just $ Op2 knownRepr $ W4.floatLe @_ @Prec32
  "ffma" -> Just $ Op4 knownRepr $ \sym r x y z -> U.withRounding sym r $ \rm ->
    W4.floatFMA @_ @Prec64 sym rm x y z
  "ffmas" -> Just $ Op4 knownRepr $ \sym r x y z ->
    U.withRounding sym r $ \rm -> W4.floatFMA @_ @Prec32 sym rm x y z
  _ -> Nothing

-- | Verify a list of arguments has a single argument and
-- return it, else raise an error.
readOneArg ::
  (W4.IsSymExprBuilder sym,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (W4.SymExpr sym),
    MonadIO m)
  => [SExp]
  -> m (Some (W4.SymExpr sym))
readOneArg operands = do
  args <- readExprs operands
  case args of
    [arg] -> return arg
    _ -> E.throwError $ printf "expecting 1 argument, got %d" (length args)

-- | Verify a list of arguments has two arguments and return
-- it, else raise an error.
readTwoArgs ::
  (W4.IsSymExprBuilder sym,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (W4.SymExpr sym),
    MonadIO m)
  => [SExp]
  -> m (Some (W4.SymExpr sym), Some (W4.SymExpr sym))
readTwoArgs operands = do
  args <- readExprs operands
  case args of
    [arg1, arg2] -> return (arg1, arg2)
    _ -> E.throwError $ printf "expecting 2 arguments, got %d" (length args)

-- | Verify a list of arguments has three arguments and
-- return it, else raise an error.
readThreeArgs ::
  (W4.IsSymExprBuilder sym,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (W4.SymExpr sym),
    MonadIO m)
  => [SExp]
  -> m (Some (W4.SymExpr sym), Some (W4.SymExpr sym), Some (W4.SymExpr sym))
readThreeArgs operands = do
  args <- readExprs operands
  case args of
    [arg1, arg2, arg3] -> return (arg1, arg2, arg3)
    _ -> E.throwError $ printf "expecting 3 arguments, got %d" (length args)



-- | Reads an "application" form, i.e. @(operator operands ...)@.
readApp ::
  forall sym m sh.
  (W4.IsSymExprBuilder sym,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (W4.SymExpr sym),
    MonadIO m)
  => SExp
  -> [SExp]
  -> m (Some (W4.SymExpr sym))
readApp opRaw@(S.WFSAtom (AIdent operator)) operands = do
  sym <- MR.reader getSym
  prefixError ("in reading expression:\n"
               ++(T.unpack $ printSExpr mempty $ S.WFSList (opRaw:operands))++"\n") $
  -- Parse an expression of the form @(fnname operands ...)@
    case lookupOp operator of
      Just (Op1 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 ->
            liftIO (Some <$> fn sym arg1)
          _ -> error "Unable to unpack Op1 arg in Formula.Parser readApp"
      Just (Op2 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 Ctx.:> arg2 ->
              liftIO (Some <$> fn sym arg1 arg2)
          _ -> error "Unable to unpack Op2 arg in Formula.Parser readApp"
      Just (Op3 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 Ctx.:> arg2 Ctx.:> arg3 ->
              liftIO (Some <$> fn sym arg1 arg2 arg3)
          _ -> error "Unable to unpack Op3 arg in Formula.Parser readApp"
      Just (Op4 arg_types fn) -> do
        args <- readExprs operands
        exprAssignment arg_types args >>= \case
          Ctx.Empty Ctx.:> arg1 Ctx.:> arg2 Ctx.:> arg3 Ctx.:> arg4 ->
              liftIO (Some <$> fn sym arg1 arg2 arg3 arg4)
          _ -> error "Unable to unpack Op4 arg in Formula.Parser readApp"
      Just (BVOp1 op) -> do
        Some expr <- readOneArg operands
        BVProof _ <- getBVProof expr
        liftIO $ Some <$> op sym expr
      Just (BVOp2 op) -> do
        (Some arg1, Some arg2)  <- readTwoArgs operands
        BVProof m <- prefixError "in arg 1: " $ getBVProof arg1
        BVProof n <- prefixError "in arg 2: " $ getBVProof arg2
        case testEquality m n of
          Just Refl -> liftIO (Some <$> op sym arg1 arg2)
          Nothing -> E.throwError $ printf "arguments to %s must be the same length, \
                                         \but arg 1 has length %s \
                                         \and arg 2 has length %s"
                                         operator
                                         (show m)
                                         (show n)
      Just (BVComp2 op) -> do
        (Some arg1, Some arg2)  <- readTwoArgs operands
        BVProof m <- prefixError "in arg 1: " $ getBVProof arg1
        BVProof n <- prefixError "in arg 2: " $ getBVProof arg2
        case testEquality m n of
          Just Refl -> liftIO (Some <$> op sym arg1 arg2)
          Nothing -> E.throwError $ printf "arguments to %s must be the same length, \
                                         \but arg 1 has length %s \
                                         \and arg 2 has length %s"
                                         operator
                                         (show m)
                                         (show n)
      Nothing ->
        -- Operators/syntactic-forms with types too
        -- complicated to nicely fit in the Op type
        case operator of
          "concat" -> do
            (Some arg1, Some arg2)  <- readTwoArgs operands
            BVProof _ <- prefixError "in arg 1: " $ getBVProof arg1
            BVProof _ <- prefixError "in arg 2: " $ getBVProof arg2
            liftIO (Some <$> W4.bvConcat sym arg1 arg2)
          "=" -> do
            (Some arg1, Some arg2)  <- readTwoArgs operands
            case testEquality (W4.exprType arg1) (W4.exprType arg2) of
              Just Refl -> liftIO (Some <$> W4.isEq sym arg1 arg2)
              Nothing -> E.throwError $
                printf "arguments must have same types, \
                       \but arg 1 has type %s \
                       \and arg 2 has type %s"
                (show (W4.exprType arg1))
                (show (W4.exprType arg2))
          "ite" -> do
            (Some test, Some then_, Some else_)  <- readThreeArgs operands
            case W4.exprType test of
              BaseBoolRepr ->
                case testEquality (W4.exprType then_) (W4.exprType else_) of
                  Just Refl -> liftIO (Some <$> W4.baseTypeIte sym test then_ else_)
                  Nothing -> E.throwError $
                    printf "then and else branches must have same type, \
                           \but then has type %s \
                           \and else has type %s"
                    (show (W4.exprType then_))
                    (show (W4.exprType else_))
              tp -> E.throwError $ printf "test expression must be a boolean; got %s" (show tp)
          "select" -> do
            (Some arr, Some idx)  <- readTwoArgs operands
            ArraySingleDim _ <- expectArrayWithIndex (W4.exprType idx) (W4.exprType arr)
            let idx' = Ctx.empty Ctx.:> idx
            liftIO (Some <$> W4.arrayLookup sym arr idx')
          "store" -> do
            (Some arr, Some idx, Some expr)  <- readThreeArgs operands
            ArraySingleDim resRepr <- expectArrayWithIndex (W4.exprType idx) (W4.exprType arr)
            case testEquality resRepr (W4.exprType expr) of
              Just Refl ->
                let idx' = Ctx.empty Ctx.:> idx
                in liftIO (Some <$> W4.arrayUpdate sym arr idx' expr)
              Nothing -> E.throwError $ printf "Array result type %s does not match %s"
                         (show resRepr)
                         (show (W4.exprType expr))
          "updateArray" -> do
            (Some arr, Some idx, Some expr)  <- readThreeArgs operands
            ArraySingleDim resRepr <- expectArrayWithIndex (W4.exprType idx) (W4.exprType arr)
            case testEquality resRepr (W4.exprType expr) of
              Just Refl ->
                let idx' = Ctx.empty Ctx.:> idx
                in liftIO (Some <$> W4.arrayUpdate sym arr idx' expr)
              Nothing -> E.throwError $ printf "Array result type %s does not match %s"
                         (show resRepr)
                         (show (W4.exprType expr))
          "field" -> do
            case operands of
              [rawStruct, S.WFSAtom (AInt rawIdx)] -> do
                Some struct  <- readExpr rawStruct
                case W4.exprType struct of
                  (BaseStructRepr fldTpReprs) ->
                    case Ctx.intIndex (fromInteger rawIdx) (Ctx.size fldTpReprs) of
                      Just (Some i) -> liftIO (Some <$> W4.structField sym struct i)
                      Nothing -> E.throwError $
                        unwords ["invalid struct index, got", show fldTpReprs, "and", show rawIdx]
                  srepr -> E.throwError $ unwords ["expected a struct, got", show srepr]
              _ -> E.throwError $ unwords ["expected an arg and an Int, got", show operands]
          "struct" -> do
            case operands of
              [S.WFSList rawFldExprs] -> do
                Some flds <- readExprsAsAssignment rawFldExprs
                liftIO (Some <$> W4.mkStruct sym flds)
              _ -> E.throwError $ unwords ["struct expects a single operand, got", show operands]
          "sbvToInteger" -> do
            (Some arg) <- readOneArg operands
            BVProof _ <- getBVProof arg
            liftIO $ Some <$> W4.sbvToInteger sym arg
          "bvToInteger" -> do
            (Some arg) <- readOneArg operands
            BVProof _ <- getBVProof arg
            liftIO $ Some <$> W4.bvToInteger sym arg
          "integerToBV" -> do
            case operands of
              [S.WFSAtom (ANat width), rawValExpr] -> do
                Some x <- readExpr rawValExpr
                case (mkNatRepr width, W4.exprType x) of
                  (Some w, BaseIntegerRepr)
                    | Just LeqProof <- isPosNat w -> do
                    liftIO (Some <$> W4.integerToBV sym x w)
                  srepr -> E.throwError $ unwords ["expected a non-zero natural and an integer, got", show srepr]
              _ -> E.throwError $ unwords ["integerToBV expects two operands, the first of which is a nat, got", show operands]
          _ -> E.throwError $ printf "couldn't parse application of %s" (printSExpr mempty opRaw)
-- Parse an expression of the form @((_ extract i j) x)@.
readApp (S.WFSList [S.WFSAtom (AIdent "_"), S.WFSAtom (AIdent "extract"), S.WFSAtom (AInt iInt), S.WFSAtom (AInt jInt)])
  args = prefixError "in reading extract expression: " $ do
  sym <- MR.reader getSym
  (Some arg) <- readOneArg args
  -- The SMT-LIB spec represents extracts differently than Crucible does. Per
  -- SMT: "extraction of bits i down to j from a bitvector of size m to yield a
  -- new bitvector of size n, where n = i - j + 1". Per Crucible:
  --
  -- > -- | Select a subsequence from a bitvector.
  -- > bvSelect :: (1 <= n, idx + n <= w)
  -- >          => sym
  -- >          -> NatRepr idx  -- ^ Starting index, from 0 as least significant bit
  -- >          -> NatRepr n    -- ^ Number of bits to take
  -- >          -> SymBV sym w  -- ^ Bitvector to select from
  -- >          -> IO (SymBV sym n)
  --
  -- The "starting index" seems to be from the bottom, so that (in slightly
  -- pseudocode)
  --
  -- > > bvSelect sym 0 8 (0x01020304:[32])
  -- > 0x4:[8]
  -- > > bvSelect sym 24 8 (0x01020304:[32])
  -- > 0x1:[8]
  --
  -- Thus, n = i - j + 1, and idx = j.
  let nInt = iInt - jInt + 1
      idxInt = jInt
  Some nNat <- prefixError "in calculating extract length: " $ intToNatM nInt
  Some idxNat <- prefixError "in extract lower bound: " $ intToNatM idxInt
  LeqProof <- fromMaybeError "extract length must be positive" $ isPosNat nNat
  BVProof lenNat <- getBVProof arg
  LeqProof <- fromMaybeError "invalid extract for given bitvector" $
    testLeq (addNat idxNat nNat) lenNat
  liftIO (Some <$> W4.bvSelect sym idxNat nNat arg)
-- Parse an expression of the form @((_ zero_extend i) x)@ or @((_ sign_extend i) x)@.
readApp (S.WFSList [S.WFSAtom (AIdent "_"), S.WFSAtom (AIdent extend), S.WFSAtom (AInt iInt)])
  args
  | extend == "zero_extend" ||
    extend == "sign_extend" = prefixError (printf "in reading %s expression: " extend) $ do
      sym <- MR.reader getSym
      Some arg <- readOneArg args
      Some iNat <- intToNatM iInt
      iPositive <- fromMaybeError "must extend by a positive length" $ isPosNat iNat
      BVProof lenNat <- getBVProof arg
      let newLen = addNat lenNat iNat
      liftIO $ withLeqProof (leqAdd2 (leqRefl lenNat) iPositive) $
        let op = if extend == "zero_extend" then W4.bvZext else W4.bvSext
        in Some <$> op sym newLen arg
-- | Parse an expression of the form:
--
-- > ((_ call "undefined") "bv" size)
--
-- This has to be separate from the normal uninterpreted functions because the
-- type is determined by the arguments.
readApp (S.WFSList [S.WFSAtom (AIdent "_"), S.WFSAtom (AIdent "call"), S.WFSAtom (AString "uf.undefined")])
  operands = do
  (Some ex) <- readOneArg operands
  case W4.exprType ex of
    BaseBVRepr {}
      | Just size <- W4.asUnsignedBV ex -> do
          sym <- MR.reader getSym
          case NR.someNat ((fromIntegral size) :: Integer) of
            Just (Some nr) -> mkUndefined nr sym
            Nothing -> E.throwError $ printf "Invalid size for undefined value: %d" size
    ety -> E.throwError $ printf "Invalid expr type: %s" (show ety)
  where
    mkUndefined :: NR.NatRepr n -> sym -> m (Some (W4.SymExpr sym))
    mkUndefined nr sym = do
      case NR.testLeq (knownNat @1) nr of
        Just NR.LeqProof -> do
          let rty = BaseBVRepr nr
          fn <- liftIO (W4.freshTotalUninterpFn sym (U.makeSymbol "uf.undefined") Ctx.empty rty)
          assn <- exprAssignment (W4.fnArgTypes fn) []
          Some <$> liftIO (W4.applySymFn sym fn assn)
        Nothing -> E.throwError $ printf "Invalid size for undefined value: %d" (NR.widthVal nr)
-- Parse an expression of the form @((_ call "foo") x y ...)@
readApp (S.WFSList [S.WFSAtom (AIdent "_"), S.WFSAtom (AIdent "call"), S.WFSAtom (AString fnName)])
  operands =
  prefixError ("in reading call '" <> fnName <> "' expression: ") $ do
    sym <- MR.reader getSym
    fns <- MR.reader getFnEnv
    SomeSome fn <- case Map.lookup fnName fns of
      Just fn -> return fn
      Nothing ->
        let template = case take 3 fnName of
              "uf." -> "uninterpreted function '%s' is not defined"
              "df." -> "library function '%s' is not defined"
              _     -> "unrecognized function prefix: '%s'"
        in E.throwError $ printf template fnName
    args <- readExprs operands
    assn <- exprAssignment (W4.fnArgTypes fn) (reverse args)
    liftIO (Some <$> W4.applySymFn sym fn assn)
readApp opRaw _ = E.throwError $ printf "couldn't parse application of %s" (printSExpr mempty opRaw)



-- | Try converting an 'Integer' to a 'NatRepr' or throw an error if not
-- possible.
intToNatM :: (E.MonadError String m) => Integer -> m (Some NatRepr)
intToNatM = fromMaybeError "integer must be non-negative to be a nat" . someNat



data ArrayJudgment :: BaseType -> BaseType -> Type where
  ArraySingleDim :: forall idx res.
                    BaseTypeRepr res
                 -> ArrayJudgment idx (BaseArrayType (Ctx.SingleCtx idx) res)

expectArrayWithIndex :: (E.MonadError String m) => BaseTypeRepr tp1 -> BaseTypeRepr tp2 -> m (ArrayJudgment tp1 tp2)
expectArrayWithIndex dimRepr (BaseArrayRepr idxTpReprs resRepr) =
  case Ctx.viewAssign idxTpReprs of
    Ctx.AssignExtend rest idxTpRepr ->
      case Ctx.viewAssign rest of
        Ctx.AssignEmpty ->
          case testEquality idxTpRepr dimRepr of
            Just Refl -> return $ ArraySingleDim resRepr
            Nothing -> E.throwError $ unwords ["Array index type", show idxTpRepr,
                                               "does not match", show dimRepr]
        _ -> E.throwError "multidimensional arrays are not supported"
expectArrayWithIndex _ repr = E.throwError $ unwords ["expected an array, got", show repr]


exprAssignment' :: (E.MonadError String m,
                    W4.IsExpr ex)
                => Ctx.Assignment BaseTypeRepr ctx
                -> [Some ex]
                -> Int
                -> Int
                -> m (Ctx.Assignment ex ctx)
exprAssignment' (Ctx.viewAssign -> Ctx.AssignEmpty) [] _ _ = return Ctx.empty
exprAssignment' (Ctx.viewAssign -> Ctx.AssignExtend restTps tp) (Some e : restExprs) idx len = do
  Refl <- case testEquality tp (W4.exprType e) of
            Just pf -> return pf
            Nothing -> E.throwError ("unexpected type in index " ++ (show idx) ++ " (total length " ++ (show len)
                                     ++ "), assigning to: " ++ show tp ++ " from expr: " ++ show (W4.exprType e))
  restAssn <- exprAssignment' restTps restExprs (idx + 1) len
  return $ restAssn Ctx.:> e
exprAssignment' _ _ _  _ = E.throwError "mismatching numbers of arguments"

exprAssignment :: (E.MonadError String m,
                   W4.IsExpr ex)
               => Ctx.Assignment BaseTypeRepr ctx
               -> [Some ex]
               -> m (Ctx.Assignment ex ctx)
exprAssignment tpAssn exs = exprAssignment' tpAssn (reverse exs) 0 (Ctx.sizeInt $ Ctx.size tpAssn)



-- | Given the s-expressions for the bindings and body of a
-- let, parse the bindings into the Reader monad's state and
-- then parse the body with those newly bound variables.
readLetExpr ::
  forall sym m sh
  . (W4.IsSymExprBuilder sym,
      Monad m,
      E.MonadError String m,
      MR.MonadReader (DefsInfo sym sh) m,
      ShowF (W4.SymExpr sym),
      MonadIO m)
  => [SExp]
  -- ^ Bindings in a let-expression.
  -> SExp
  -- ^ Body of the let-expression.
  -> m (Some (W4.SymExpr sym))
readLetExpr [] body = readExpr body
readLetExpr ((S.WFSList [S.WFSAtom (AIdent x), e]):rst) body = do
  v <- readExpr e
  MR.local (\r -> r {getLetBindings = (Map.insert x v) $ getLetBindings r}) $
    readLetExpr rst body
readLetExpr bindings _body = E.throwError $
  "invalid s-expression for let-bindings: " ++ (show bindings)

-- | Parse an arbitrary expression.
readExpr :: forall sym m sh
          . (W4.IsSymExprBuilder sym,
             Monad m,
             E.MonadError String m,
             MR.MonadReader (DefsInfo sym sh) m,
             ShowF (W4.SymExpr sym),
             MonadIO m)
         => SExp
         -> m (Some (W4.SymExpr sym))
readExpr (S.WFSAtom (AInt n)) = do
  sym <- MR.reader getSym
  liftIO $ (Some <$> W4.intLit sym n)
readExpr (S.WFSAtom (ANat n)) = do
  sym <- MR.reader getSym
  liftIO $ (Some <$> W4.natLit sym n)
readExpr (S.WFSAtom (ABool b)) = do
  sym <- MR.reader getSym
  liftIO $ return $ Some $ W4.backendPred sym b
readExpr (S.WFSAtom (AString _)) = error $ "TODO: support readExpr for string literals"
readExpr (S.WFSAtom (AReal _)) = error $ "TODO: support readExpr for real literals"
readExpr (S.WFSAtom (ABV len val)) = do
  -- This is a bitvector literal.
  sym <- MR.reader getSym
  -- The following two patterns should never fail, given that during parsing we
  -- can only construct BVs with positive length.
  case someNat (toInteger len) of
    Just (Some lenRepr) ->
        let Just pf = isPosNat lenRepr
        in liftIO $ withLeqProof pf (Some <$> W4.bvLit sym lenRepr val)
    Nothing -> error "SemMC.Formula.Parser.readExpr someNat failure"
  -- Just (Some lenRepr) <- return $ someNat (toInteger len)
  -- let Just pf = isPosNat lenRepr
  -- liftIO $ withLeqProof pf (Some <$> W4.bvLit sym lenRepr val)
-- Let-bound variable
readExpr (S.WFSAtom (AIdent name)) = do
  maybeBinding <- MR.asks $ (Map.lookup name) . getLetBindings
  -- We first check the local lexical environment (i.e., the
  -- in-scope let-bindings) before consulting the "global"
  -- scope.
  case maybeBinding of
    -- simply return it's let-binding
    Just binding -> return binding
    Nothing -> do
      DefsInfo { getArgNameList = argNames
               , getSym = sym
               , getArgVarList = argVars
               , getBaseEnv = baseEnv
               } <- MR.ask
      var <- readVariable @sym (\nm -> Map.lookup nm baseEnv) argNames name
      case var of
        Some (ParsedArgument _ idx) ->
          return . Some . W4.varExpr sym $ (argVars Ctx.! idx)
        Some (ParsedGlobal expr) -> return $ Some expr
readExpr (S.WFSList ((S.WFSAtom (AIdent "let")):rhs)) =
  case rhs of
    [S.WFSList bindings, body] -> readLetExpr bindings body
    _ -> E.throwError "ill-formed let s-expression"
readExpr (S.WFSList []) = E.throwError "ill-formed empty s-expression"
readExpr (S.WFSList (operator:operands)) = readApp operator operands



-- | Parse multiple expressions in a list.
readExprs :: (W4.IsSymExprBuilder sym,
              Monad m,
              E.MonadError String m,
              MR.MonadReader (DefsInfo sym sh) m,
              ShowF (W4.SymExpr sym),
              MonadIO m)
          => [SExp]
          -> m [Some (W4.SymExpr sym)]
readExprs [] = return []
readExprs (e:rest) = do
  e' <- readExpr e
  rest' <- readExprs rest
  return $ e' : rest'

readExprsAsAssignment ::
  forall sym m sh .
  (W4.IsSymExprBuilder sym,
    Monad m,
    E.MonadError String m,
    MR.MonadReader (DefsInfo sym sh) m,
    ShowF (W4.SymExpr sym),
    MonadIO m)
  => [SExp]
  -> m (Some (Ctx.Assignment (W4.SymExpr sym)))
readExprsAsAssignment [] = return $ Some Ctx.empty
readExprsAsAssignment (s:rest) = do
  Some e <- readExpr s
  Some ss <- readExprsAsAssignment rest
  return $ Some (Ctx.extend ss e)


buildArgumentList :: forall m
                    . (E.MonadError String m)
                   => [SExp]
                   -> m (Some (Ctx.Assignment ArgData))
buildArgumentList sexpr =
  case sexpr of
    [] -> return $ Some (Ctx.empty)
    (s:rest) -> do
      (operand, tyRaw) <- case s of
        S.WFSList [(S.WFSAtom (AIdent arg)), ty]
          -> return (arg, ty)
        _ -> E.throwError $ "Expected (operand . 'type) pair: " ++ show s
      Some tp <- readBaseType tyRaw
      Some rest' <- buildArgumentList rest
      return $ Some (rest' Ctx.:> (ArgData operand tp))

readSymFn' :: forall sym m
           . (W4.IsExprBuilder sym,
              W4.IsSymExprBuilder sym,
              E.MonadError String m,
              MonadIO m,
              ShowF (W4.SymExpr sym),
              U.HasLogCfg)
          => ParserConfig sym
          -> SExp
          -> m (SomeSome (W4.SymFn sym))
readSymFn' cfg sexpr =
  let
    sym = pSym cfg
    fnEnv = pSymFnEnv cfg
    baseEnv = pBaseEnv cfg
  in do
  (name, symFnInfoRaw) <- case sexpr of
    S.WFSList [S.WFSAtom (AIdent "symfn"), S.WFSAtom (AString nm), info] -> return (nm, info)
    _ -> E.throwError ("invalid top-level function definition structure:\n" ++ show sexpr)

  let symbol = U.makeSymbol name
  case symFnInfoRaw of
    S.WFSList [S.WFSAtom (AIdent "definedfn"), argTsRaw, retTRaw, S.WFSList argVarsRaw, exprRaw]
      -> do
        Some argTs <- readBaseTypes argTsRaw
        Some retT <- readBaseType retTRaw
        let ufname = "uf." ++ name
        -- For recursive calls, we may need an uninterpreted variant of this function
        fnEnv' <- case Map.lookup ufname fnEnv of
          Just (U.SomeSome ufsymFn) ->
            if | Just Refl <- testEquality argTs (W4.fnArgTypes ufsymFn)
               , Just Refl <- testEquality retT (W4.fnReturnType ufsymFn) -> return fnEnv
               | otherwise -> E.throwError $ "Bad signature for existing function: " ++ show name
          Nothing -> do
            symFn <- liftIO $ W4.freshTotalUninterpFn sym symbol argTs retT
            return $ Map.insert ufname (U.SomeSome symFn) fnEnv

        Some argNameList <- buildArgumentList @m argVarsRaw
        argVarList <- traverseFC mkArgumentVar argNameList
        Some expr <- MR.runReaderT (readExpr exprRaw) $
          DefsInfo { getSym = sym
                   , getFnEnv = fnEnv'
                   , getBaseEnv = baseEnv
                   , getArgVarList = argVarList
                   , getArgNameList = argNameList
                   , getLetBindings = Map.empty
                   }
        let expand args = allFC W4.baseIsConcrete args
        symFn <- liftIO $ W4.definedFn sym symbol argVarList expr expand
        return $ SomeSome symFn
    S.WFSList [S.WFSAtom (AIdent "uninterpfn"), argTsRaw, retTRaw]
      -> do
        Some argTs <- readBaseTypes argTsRaw
        Some retT <- readBaseType retTRaw
        case Map.lookup ("uf."++name) fnEnv of
          Just (SomeSome symFn) -> do
            let argTs' = W4.fnArgTypes symFn
            let retT' = W4.fnReturnType symFn
            if | Just Refl <- testEquality argTs argTs'
               , Just Refl <- testEquality retT retT' -> do
                 return $ SomeSome symFn
               | otherwise -> E.throwError "invalid function signature in environment"
          _ -> do
            symFn <- liftIO $ W4.freshTotalUninterpFn sym symbol argTs retT
            return $ SomeSome symFn
    _ -> E.throwError "invalid function definition info structure"
        
  where    
    mkArgumentVar :: forall tp. ArgData tp -> m (W4.BoundVar sym tp)
    mkArgumentVar (ArgData varName tpRepr) =
      let symbol = U.makeSymbol varName
      in liftIO $ W4.freshBoundVar (pSym cfg) symbol tpRepr

genRead :: forall a
         . U.HasLogCfg
        => String
        -> (SExp -> E.ExceptT String IO a)
        -> T.Text
        -> IO (Either String a)
genRead callnm m text = E.runExceptT $ go
  where
    go = do
      sexpr <- case parseSExpr text of
                 Left err -> E.throwError err
                 Right res -> return res
      let firstLine = show $ fmap T.unpack $ take 1 $ T.lines text
      liftIO $ U.logIO U.Info $
        callnm ++ " of " ++ (show $ T.length text) ++ " bytes " ++ firstLine
      m sexpr


-- BOOKMARK / TODO / FIXME Do we want a
--  pGlobalEnv :: Map T.Text -> Either (Some (W4.SymExpr t)) (SomeSome (W4.SymFn t))
-- OR just
-- pGlobalEnv :: Map T.Text -> (Some (W4.SymExpr t))
-- (i.e., can / should SymFns be stuffed into regular SymExprs? we're doing that with everything
-- else... but perhaps functions are special because they're not first class values
-- in What4? I.e., there's no BaseType for a function type (right?))
data ParserConfig sym = ParserConfig
  { pSym :: sym
  -- ^ The symbolic What4 backend being used.
  , pSymFnEnv :: SymFnEnv sym
  -- ^ The environment of defined What4 SymFns.
  , pBaseEnv :: BaseEnv sym
  -- ^ The environment of defined variables with What4 BaseTypes.
  }
  -- N.B. these were removed:
  -- , pGlobalLookup :: T.Text -> IO (Maybe (Some (W4.SymExpr t)))
  -- , pOverrides :: String -> Maybe ([Some (W4.SymExpr t)] -> IO (Either String (Some (W4.SymExpr t))))

type SymFnEnv sym = Map String (SomeSome (W4.SymFn sym))
type BaseEnv sym = Map String (Some (W4.SymExpr sym))

defaultParserConfig :: t -> ParserConfig t
defaultParserConfig t =
  ParserConfig { pSym = t
               , pSymFnEnv = Map.empty
               , pBaseEnv = Map.empty
               }

readSymFn :: forall sym
           . (W4.IsExprBuilder sym,
              W4.IsSymExprBuilder sym,
              ShowF (W4.SymExpr sym),
              U.HasLogCfg)
          => ParserConfig sym
          -> T.Text
          -> IO (Either String (SomeSome (W4.SymFn sym)))
readSymFn cfg = genRead "readSymFn" (readSymFn' cfg)

readSymFnFromFile :: forall sym
                   . (W4.IsExprBuilder sym,
                      W4.IsSymExprBuilder sym,
                      ShowF (W4.SymExpr sym),
                      U.HasLogCfg)
                  => ParserConfig sym
                  -> FilePath
                  -> IO (Either String (SomeSome (W4.SymFn sym)))
readSymFnFromFile cfg fp = do
  liftIO $ U.logIO U.Info $ "readSymFnFromFile " ++ fp
  readSymFn cfg =<< T.readFile fp

readSymFnEnv' :: forall sym m
               . (W4.IsExprBuilder sym,
                  W4.IsSymExprBuilder sym,
                  E.MonadError String m,
                  MonadIO m,
                  ShowF (W4.SymExpr sym),
                  U.HasLogCfg)
              => ParserConfig sym
              -> SExp
              -> m (SymFnEnv sym)
readSymFnEnv' cfg sexpr = do
  symFnEnvRaw <- case sexpr of
    S.WFSList [S.WFSAtom (AIdent "symfnenv"), S.WFSList symFnEnvRaw] -> return symFnEnvRaw
    _ -> E.throwError "invalid top-level function environment structure"
  readSymFns (pSymFnEnv cfg) symFnEnvRaw
  where
    readSymFns ::
      SymFnEnv sym
      -> [SExp]
      -> m (SymFnEnv sym)
    readSymFns env sexprs = case sexprs of
      [] -> return env
      (s:rest) -> do
        (nm, symFn) <- readSomeSymFn env s
        let env' = Map.insert nm symFn env
        readSymFns env' rest
      
    readSomeSymFn ::
      SymFnEnv sym
      -> SExp
      -> m (String, (SomeSome (W4.SymFn sym)))
    readSomeSymFn env sexpr' = do
      (name, rawSymFn) <- case sexpr' of
        S.WFSList [(S.WFSAtom (AString name)), rawSymFn] -> return (name, rawSymFn)
        _ -> E.throwError $ "invalid function environment structure: " ++ show sexpr'
      ssymFn <- readSymFn' (cfg { pSymFnEnv = env }) rawSymFn
      return (name, ssymFn)

readSymFnEnv :: forall sym
           . (W4.IsExprBuilder sym,
              W4.IsSymExprBuilder sym,
              ShowF (W4.SymExpr sym),
              U.HasLogCfg)
          => ParserConfig sym
          -> T.Text
          -> IO (Either String (SymFnEnv sym))
readSymFnEnv cfg = genRead "readSymFnEnv" (readSymFnEnv' cfg)

readSymFnEnvFromFile :: forall sym
                   . (W4.IsExprBuilder sym,
                      W4.IsSymExprBuilder sym,
                      ShowF (W4.SymExpr sym),
                      U.HasLogCfg)
                  => ParserConfig sym
                  -> FilePath
                  -> IO (Either String (SymFnEnv sym))
readSymFnEnvFromFile cfg fp = do
  liftIO $ U.logIO U.Info $ "readSymFnEnvFromFile " ++ fp
  readSymFnEnv cfg =<< T.readFile fp
