{-# Language ImplicitParams #-}
{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
module Main(main) where

import Data.String(fromString)
import qualified Data.Foldable as Fold
import Data.Maybe(catMaybes)
import qualified Data.Map as Map
import Control.Lens((^.))
import Control.Monad.ST(RealWorld, stToIO)
import Control.Monad(unless)
import System.IO(hPutStrLn,stdout,stderr)
import System.Environment(getProgName,getArgs)
import System.FilePath(takeExtension)

import Control.Monad.State(evalStateT)

import Data.Parameterized.Nonce(withIONonceGenerator)
import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Context(pattern Empty)

import Text.LLVM.AST(Module)
import Data.LLVM.BitCode (parseBitCodeFromFile)

import What4.Solver.Adapter(SolverAdapter(..))
import What4.Config (extendConfig)
import What4.Interface(getConfiguration)

import Lang.Crucible.Backend
  (getProofObligations,IsSymInterface, pushAssumptionFrame, popAssumptionFrame)
import Lang.Crucible.Backend.Online(withOnlineBackend)
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(SomeCFG(..), AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle(newHandleAllocator,HandleAllocator)
import Lang.Crucible.Simulator.RegMap(emptyRegMap,regValue)
import Lang.Crucible.Simulator.ExecutionTree
        ( initSimContext
        , ExecResult(..)
        , ErrorHandler(..)
        , stateTree
        , activeFrames
        )
import Lang.Crucible.Simulator.OverrideSim
        ( fnBindingsFromList, initSimState, runOverrideSim, callCFG)

import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals, registerModuleFn, LLVM)
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, initializeMemory
        , transContext, cfgMap, initMemoryCFG
        , LLVMContext
        , ModuleCFGMap
        )
import Lang.Crucible.LLVM.Types(withPtrWidth)
import Lang.Crucible.LLVM.Intrinsics
          (llvmIntrinsicTypes, llvmPtrWidth, register_llvm_overrides)



import Error
import Goal
import Types
import Overrides
import Model
import Clang
import Log
import Options

main :: IO ()
main =
  do args <- getArgs
     case args of
       file : _ ->
          do opts <- testOptions file
             do unless (takeExtension file == ".bc") (genBitCode opts)
                checkBC opts `catch` errHandler opts
           `catch` \e -> sayFail "Crux" (ppError e)
       _ -> do p <- getProgName
               hPutStrLn stderr $ unlines
                  [ "Usage:"
                  , "  " ++ p ++ " FILE.bc"
                  ]


errHandler :: Options -> Error -> IO ()
errHandler opts e =
  do sayFail "Crux" (ppError e)
     case e of
       FailedToProve _ (Just c) -> buildModelExes opts c
       _ -> return ()
    `catch` \e1 -> sayFail "Crux" (ppError e1)

checkBC :: Options -> IO ()
checkBC opts =
  do let file = optsBCFile opts
     say "Crux" ("Checking " ++ show file)
     errs <- simulate file (checkFun "main")
     case catMaybes errs of
      [] -> sayOK "Crux" "Valid."
      (e : _) -> errHandler opts e

-- | Create a simulator context for the given architecture.
setupSimCtxt ::
  (ArchOk arch, IsSymInterface sym) =>
  HandleAllocator RealWorld ->
  sym ->
  SimCtxt sym arch
setupSimCtxt halloc sym =
  initSimContext sym
                 llvmIntrinsicTypes
                 halloc
                 stdout
                 (fnBindingsFromList [])
                 llvmExtensionImpl
                 emptyModel


-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO Module
parseLLVM file =
  do ok <- parseBitCodeFromFile file
     case ok of
       Left err -> throwError (LLVMParseError err)
       Right m  -> return m


setupMem ::
  (ArchOk arch, IsSymInterface sym) =>
  LLVMContext arch ->
  ModuleTranslation arch ->
  OverM sym arch ()
setupMem ctx mtrans =
  do -- register the callable override functions
     evalStateT register_llvm_overrides ctx

     -- initialize LLVM global variables
     -- XXX: this might be wrong: only RO globals should be set
     _ <- case initMemoryCFG mtrans of
            SomeCFG initCFG -> callCFG initCFG emptyRegMap

      -- register all the functions defined in the LLVM module
     mapM_ registerModuleFn $ Map.toList $ cfgMap mtrans


simulate ::
  FilePath ->
  (forall scope arch.
      ArchOk arch => ModuleCFGMap arch -> OverM scope arch ()
  ) ->
  IO [Maybe Error]
simulate file k =
  do llvm_mod   <- parseLLVM file
     halloc     <- newHandleAllocator
     Some trans <- stToIO (translateModule halloc llvm_mod)
     let llvmCtxt = trans ^. transContext

     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $
       withIONonceGenerator $ \nonceGen ->
       withOnlineBackend nonceGen $ \sym ->
       do -- set up configuration options
          let cfg = getConfiguration sym
          extendConfig (solver_adapter_config_options prover) cfg

          frm <- pushAssumptionFrame sym
          let simctx = setupSimCtxt halloc sym

          mem  <- initializeMemory sym llvmCtxt llvm_mod
          let globSt = llvmGlobals llvmCtxt mem
          let simSt  = initSimState simctx globSt eHandler

          res <- runOverrideSim simSt UnitRepr $
                   do setupMem llvmCtxt trans
                      setupOverrides llvmCtxt
                      k (cfgMap trans)

          _ <- popAssumptionFrame sym frm

          case res of
            FinishedExecution ctx' _ ->
              do gs <- Fold.toList <$> getProofObligations sym
                 mapM (proveGoal ctx') gs
            AbortedResult _ err -> throwError (SimAbort err)

eHandler :: ErrorHandler (Model sym) sym (LLVM arch) trp
eHandler = EH (\e st -> throwError (SimFail e (activeFrames (st ^. stateTree))))

checkFun :: ArchOk arch => String -> ModuleCFGMap arch -> OverM scope arch ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty -> (regValue <$> callCFG anyCfg emptyRegMap) >> return ()
        _     -> throwError BadFun
    Nothing -> throwError (MissingFun nm)

