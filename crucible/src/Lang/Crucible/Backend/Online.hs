------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Backend.Online
-- Description : A solver backend that maintains a persistent connection
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
--
-- The online backend maintains an open connection to an SMT solver
-- (Yices, currently) that is used to prune unsatisfiable execution
-- traces during simulation.  At every symbolic branch point, the SMT
-- solver is queried to determine if one or both symbolic branches are
-- unsatisfiable.  Only branches with satisfiable branch conditions
-- are explored.
--
-- The online backend also allows override definitions access to a
-- persistent SMT solver connection.  This can be useful for some
-- kinds of algorithms that benefit from quickly performing many
-- small solver queries in a tight interaction loop.
------------------------------------------------------------------------

{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
module Lang.Crucible.Backend.Online
  ( -- * OnlineBackend
    OnlineBackend
  , withOnlineBackend
    -- * OnlineBackendState
  , OnlineBackendState
  , getYicesProcess
  , Yices.YicesProcess(..)
  , yicesOnlineAdapter
  ) where

import           Control.Exception ( SomeException, throwIO, try )
import           Control.Lens
import           Control.Monad
import           Data.Bits
import           Data.Foldable
import           Data.IORef
import           Data.Parameterized.Nonce
import           System.Exit
import           System.IO
import           System.Process

import qualified What4.Config as CFG
import           What4.Solver.Adapter
import           What4.AssumptionStack as AS
import           What4.Interface
import qualified What4.Utils.Process as Proc
import           What4.SatResult
import           What4.ProblemFeatures
import           What4.Protocol.SMTWriter
  ( assumeFormula
  , mkFormula
  )
import qualified What4.Solver.Yices as Yices
import qualified What4.Expr.Builder as B

import           Lang.Crucible.Backend
import           Lang.Crucible.Simulator.SimError


type OnlineBackend t = B.ExprBuilder t OnlineBackendState

yicesOnlineAdapter :: SolverAdapter OnlineBackendState
yicesOnlineAdapter =
   Yices.yicesAdapter
   { solver_adapter_check_sat = \sym _ p cont -> do
        yproc <- getYicesProcess sym
        let c = Yices.yicesConn yproc

        -- build the formula outside the frame to
        -- preserve intermediate cache results
        p_smtformula <- mkFormula c p

        Yices.inFreshFrame c $ do
          assumeFormula c p_smtformula
          res <- Yices.checkAndGetModel yproc
          cont (fmap (\x -> (x, Nothing)) res)
   }

------------------------------------------------------------------------
-- OnlineBackendState

data YicesOnline

startYicesProcess :: CFG.Config -> IO (Yices.YicesProcess t s)
startYicesProcess cfg = do
  yices_path <- Proc.findSolverPath Yices.yicesPath cfg
  let args = ["--mode=push-pop"]

  let create_proc
        = (proc yices_path args)
          { std_in  = CreatePipe
          , std_out = CreatePipe
          , std_err = CreatePipe
          , cwd = Nothing
          }

  let startProcess = do
        x <- createProcess create_proc
        case x of
          (Just in_h, Just out_h, Just err_h, ph) -> return (in_h,out_h,err_h,ph)
          _ -> fail "Internal error in startYicesProcess: Failed to create handle."

  (in_h,out_h,err_h,ph) <- startProcess

  --void $ forkIO $ logErrorStream err_stream (logLn 2)
  -- Create new connection for sending commands to yices.
  let features = useLinearArithmetic
             .|. useBitvectors
             .|. useSymbolicArrays
             .|. useComplexArithmetic
             .|. useStructs
  conn <- Yices.newConnection in_h features B.emptySymbolVarBimap
  Yices.setYicesParams conn cfg
  err_reader <- Yices.startHandleReader err_h
  return $! Yices.YicesProcess { Yices.yicesConn   = conn
                               , Yices.yicesStdin  = in_h
                               , Yices.yicesStdout = out_h
                               , Yices.yicesStderr = err_reader
                               , Yices.yicesHandle = ph
                               }

shutdownYicesProcess :: Yices.YicesProcess t s -> IO ()
shutdownYicesProcess yices = do
  -- Close input stream.
  hClose (Yices.yicesStdin yices)
  -- Log outstream as error messages.

  --logLn 2 "Waiting for yices to terminate"
  ec <- waitForProcess (Yices.yicesHandle yices)
  case ec of
    ExitSuccess -> return () --logLn 2 "Yices terminated."
    ExitFailure x ->
       fail $ "yices exited with unexpected code: "++show x

-- | This represents the state of the backend along a given execution.
-- It contains the current assertions and program location.
data OnlineBackendState t
   = OnlineBackendState { assumptionStack :: !(AssumptionStack (B.BoolExpr t) AssumptionReason SimError)
                          -- ^ Number of times we have pushed
                        , yicesProc    :: !(IORef (Maybe (Yices.YicesProcess t YicesOnline)))
                        }

-- | Returns an initial execution state.
initialOnlineBackendState :: NonceGenerator IO t -> IO (OnlineBackendState t)
initialOnlineBackendState gen = do
  stk <- initAssumptionStack gen
  procref <- newIORef Nothing
  return $! OnlineBackendState
              { assumptionStack = stk
              , yicesProc = procref
              }

getAssumptionStack :: OnlineBackend t -> IO (AssumptionStack (B.BoolExpr t) AssumptionReason SimError)
getAssumptionStack sym = assumptionStack <$> readIORef (B.sbStateManager sym)

getYicesProcess :: OnlineBackend t -> IO (Yices.YicesProcess t YicesOnline)
getYicesProcess sym = do
  st <- readIORef (B.sbStateManager sym)
  mproc <- readIORef (yicesProc st)
  case mproc of
    Just p -> do
      return p
    Nothing -> do
      let cfg = getConfiguration sym
      p <- startYicesProcess cfg
      -- set up Yices parameters
      Yices.setYicesParams (Yices.yicesConn p) cfg
      Yices.push (Yices.yicesConn p)
      writeIORef (yicesProc st) (Just p)
      return p

withOnlineBackend :: NonceGenerator IO t
                  -> (OnlineBackend t -> IO a)
                  -> IO a
withOnlineBackend gen action = do
  st <- initialOnlineBackendState gen
  sym <- B.newExprBuilder st gen
  r <- try $ action sym
  mp <- readIORef (yicesProc st)
  case mp of
   Nothing -> return ()
   Just p -> shutdownYicesProcess p
  case r of
   Left e -> throwIO (e :: SomeException)
   Right x -> return x

checkSatisfiable
    :: OnlineBackend t
    -> B.BoolExpr t
    -> IO (SatResult ())
checkSatisfiable sym p = do
   yproc <- getYicesProcess sym
   let c = Yices.yicesConn yproc

   p_smtexpr <- mkFormula c p
   Yices.inFreshFrame c $ do
     assumeFormula c p_smtexpr
     Yices.check yproc

instance IsBoolSolver (OnlineBackend t) where
  addAssertion sym a = do
    case asConstantPred (a^.labeledPred) of
      Just True  -> return ()
      Just False -> throwIO (a^.labeledPredMsg)
      _ ->
        do conn <- Yices.yicesConn <$> getYicesProcess sym
           stk <- getAssumptionStack sym
           -- Record assertion
           AS.assert a stk
           -- Send assertion to yices
           Yices.assume conn (a^.labeledPred)

  addAssumption sym a = do
    case asConstantPred (a^.labeledPred) of
      Just True  -> return ()
      Just False -> addFailedAssertion sym InfeasibleBranchError
      _ ->
        do conn <- Yices.yicesConn <$> getYicesProcess sym
           stk <- getAssumptionStack sym
           -- Record assumption
           AS.assume a stk
           -- Send assertion to yices
           Yices.assume conn (a^.labeledPred)

  addAssumptions sym a = do
    -- Tell Yices of assertions
    conn <- Yices.yicesConn <$> getYicesProcess sym
    mapM_ (Yices.assume conn . view labeledPred) (toList a)
    -- Add assertions to list
    stk <- getAssumptionStack sym
    appendAssumptions a stk

  getPathCondition sym = do
    stk <- getAssumptionStack sym
    ps <- collectAssumptions stk
    andAllOf sym (folded.labeledPred) ps

  evalBranch sym p = do
    case asConstantPred p of
      Just True  -> return $! NoBranch True
      Just False -> return $! NoBranch False
      Nothing ->
        do notP <- notPred sym p
           p_res    <- checkSatisfiable sym p
           notp_res <- checkSatisfiable sym notP
           case (p_res, notp_res) of
             (Unsat, Unsat) -> return InfeasibleBranch
             (Unsat, _ )    -> return $ NoBranch False
             (_    , Unsat) -> return $ NoBranch True
             (_    , _)     -> return $ SymbolicBranch True

  pushAssumptionFrame sym = do
    conn <- Yices.yicesConn <$> getYicesProcess sym
    stk <- getAssumptionStack sym
    Yices.push conn
    pushFrame stk

  popAssumptionFrame sym ident = do
    conn <- Yices.yicesConn <$> getYicesProcess sym
    stk <- getAssumptionStack sym
    h <- stackHeight stk
    frm <- popFrame ident stk
    ps <- readIORef (assumeFrameCond frm)
    Yices.pop conn
    when (h == 0) (Yices.push conn)
    return ps

  getProofObligations sym = do
    stk <- getAssumptionStack sym
    AS.getProofObligations stk

  setProofObligations sym obligs = do
    stk <- getAssumptionStack sym
    AS.setProofObligations obligs stk

  addFailedAssertion sym msg = do
    loc <- getCurrentProgramLoc sym
    throwIO (SimError loc msg)

  cloneAssumptionState sym = do
    stk <- getAssumptionStack sym
    AS.cloneAssumptionStack stk

  restoreAssumptionState sym stk = do
    conn <- Yices.yicesConn <$> getYicesProcess sym
    oldstk <- getAssumptionStack sym
    h <- stackHeight oldstk
    -- NB, pop h+1 times
    forM_ [0 .. h] $ \_ -> Yices.pop conn

    frms   <- AS.allAssumptionFrames stk
    forM_ (toList frms) $ \frm ->
      do Yices.push conn
         ps <- readIORef (assumeFrameCond frm)
         forM_ (toList ps) (Yices.assume conn . view labeledPred)