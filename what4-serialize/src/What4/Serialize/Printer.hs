{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}

module What4.Serialize.Printer
  (
    printSymFn'
  , printSymFn
  , printSymFnEnv
  , convertExprWithLet
  , convertBaseType
  , convertBaseTypes
  , convertSymFn
  , convertSymFnEnv
  ) where

import qualified Data.Foldable as F
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Map.Ordered (OMap)
import qualified Data.Map.Ordered as OMap
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Nonce as Nonce
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Text as T
import           Data.Word ( Word64 )
import           Control.Monad.Trans.RWS.Strict ( RWS )
import qualified Control.Monad.Trans.RWS.Strict as RWS

import qualified Control.Monad.Writer as W

import qualified Data.SCargot.Repr.WellFormed as S

import           What4.BaseTypes
import qualified What4.Expr as W4
import qualified What4.Expr.BoolMap as BooM
import qualified What4.Expr.Builder as W4
import qualified What4.Expr.WeightedSum as WSum
import qualified What4.Interface as W4
import qualified What4.Symbol as W4
import           What4.Utils.Util ( SomeSome(..) )

import           What4.Serialize.SETokens ( Atom(..), printSExpr
                                          , ident, int, string
                                          , bitvec, bool, nat, real
                                          )

type SExp = S.WellFormedSExpr Atom
type SymFnEnv t = Map T.Text (SomeSome (W4.ExprSymFn t))

-- This file is organized top-down, i.e., from high-level to low-level.

-- | Serialize the given What4 ExprSymFn as an s-expression, and return
-- the binding environment of its function calls.
printSymFn' :: W4.ExprSymFn t args ret -> (T.Text, SymFnEnv t)
printSymFn' symfn =
  let
    (sexp, fenv) = W.runWriter $ convertSymFn symfn
  in (printSExpr mempty sexp, fenv)

printSymFn :: W4.ExprSymFn t args ret -> T.Text
printSymFn = fst . printSymFn'

printSymFnEnv :: [(T.Text, SomeSome (W4.ExprSymFn t))] -> T.Text
printSymFnEnv fenv =
  let
    (sexp, _) = W.runWriter $ convertSymFnEnv fenv
    comments = mempty
  in printSExpr comments sexp


convertSymFnEnv :: forall t. [(T.Text, SomeSome (W4.ExprSymFn t))] -> W.Writer (SymFnEnv t) SExp
convertSymFnEnv sigs = do
  sexpr <- mapM convertSomeSymFn $ sigs
  return $ S.L [ ident "symfnenv", S.L sexpr ]
  where
    convertSomeSymFn :: (T.Text, SomeSome (W4.ExprSymFn t)) -> W.Writer (SymFnEnv t) SExp
    convertSomeSymFn (name, SomeSome symFn) = do
      sexpr <- convertSymFn symFn
      return $ S.L [ string (T.unpack name), sexpr ]

convertExprWithLet :: W4.Expr t tp -> W.Writer (SymFnEnv t) SExp
convertExprWithLet expr = do
  W.tell fenv
  return $ S.L [ ident "let"
               , bindings
               , body
               ]
  where ((body, bindings), _, fenv) = runMemo $ do
          sexp <- convertExpr expr
          rawbindings <- OMap.assocs <$> RWS.get
          let sexprs = map (\(key, sexp') -> S.L [ letVar key, sexp' ]) rawbindings
          return $ (sexp, S.L sexprs)

convertSymFn :: forall t args ret
              . W4.ExprSymFn t args ret
             -> W.Writer (SymFnEnv t) SExp
convertSymFn symFn@(W4.ExprSymFn _ symFnName symFnInfo _) = do
  sexpr <- case symFnInfo of
     W4.DefinedFnInfo argVars expr _ -> do
       let sArgVars = S.L $ reverse $ FC.toListFC getBoundVar argVars
       sExpr <- convertExprWithLet expr
       let sArgTs = convertBaseTypes (W4.fnArgTypes symFn)
       let sRetT = convertBaseType (W4.fnReturnType symFn)
       return $ S.L [ ident "definedfn", sArgTs, sRetT, sArgVars, sExpr ]
     W4.UninterpFnInfo argTs retT ->
       let
         sArgTs = convertBaseTypes argTs
         sRetT = convertBaseType retT
       in return $ S.L [ ident "uninterpfn", sArgTs, sRetT]
     _ -> error "Unsupported ExprSymFn kind in convertSymFn"
  return $ S.L [ ident "symfn", string (T.unpack $ W4.solverSymbolAsText symFnName), sexpr ]
  where
    getBoundVar :: forall tp. W4.ExprBoundVar t tp -> SExp
    getBoundVar var =
       let nameExpr = ident (T.unpack (W4.solverSymbolAsText (W4.bvarName var)))
           typeExpr = convertBaseType (W4.bvarType var)
       in S.L [ nameExpr, typeExpr ]

type Memo t a = RWS () (SymFnEnv t) (OMap SKey SExp) a

runMemo ::  Memo t a -> (a, OMap SKey SExp, SymFnEnv t)
runMemo m = RWS.runRWS m () OMap.empty


-- | Key for sharing SExp construction. Internally indexes are expression nonces,
-- but the let-binding identifiers are based on insertion order to the OMap
newtype SKey = SKey {sKeyValue :: Word64}
  deriving (Eq, Ord, Show)


-- | For the let-bound variables we gensym/introduce to keep
-- things from exploding in size during serialization, we
-- add the `@l` prefix to the noce id, so it is not a valid
-- What4.Symbol.SolverSymbol and is globally unique (and
-- thus should not clash with any crucible-generated
-- variables or other let-bound variables).
letVar :: SKey -> SExp
letVar key = ident $ "@l"++(show $ sKeyValue $ key)

exprSKey :: W4.Expr t tp -> Maybe SKey
exprSKey x = SKey . Nonce.indexValue <$> W4.exprMaybeId x

-- | Don't overwrite cache entries, since the ordering needs to be preserved
addKey :: SKey -> SExp -> Memo t ()
addKey key sexp = do
  cache <- RWS.get
  RWS.put (cache OMap.|> (key, sexp))

convertExpr :: forall t tp . W4.Expr t tp -> Memo t SExp
convertExpr initialExpr = do
  case exprSKey initialExpr of
    Nothing -> go initialExpr
    Just key -> do
      cache <- RWS.get
      if OMap.member key cache
        then return $ letVar key
        else do
        sexp <- go initialExpr
        case sexp of
          S.A _ -> return sexp -- don't memoize atomic s-expressions
          _ -> do 
            addKey key sexp
            return $ letVar key
  where go :: W4.Expr t tp -> Memo t SExp
        -- TODO / FIXME - we need to serialize integers, nates, reals, etc differently
        go (W4.SemiRingLiteral W4.SemiRingNatRepr val _) = return $ nat val
        go (W4.SemiRingLiteral W4.SemiRingIntegerRepr val _) = return $ int val -- do we need/want these?
        go (W4.SemiRingLiteral W4.SemiRingRealRepr val _) = return $ real val
        go (W4.SemiRingLiteral (W4.SemiRingBVRepr _ sz) val _) = return $ bitvec (fromInteger (toInteger (widthVal sz))) val
        go (W4.StringExpr {}) = error "StringExpr is not yet supported"
        go (W4.BoolExpr b _) = return $ bool b
        go (W4.AppExpr appExpr) = convertAppExpr' appExpr
        go (W4.NonceAppExpr nae) =
          case W4.nonceExprApp nae of
            W4.FnApp fn args -> convertFnApp fn args
            W4.Forall {} -> error "Forall NonceAppExpr not supported"
            W4.Exists {} -> error "Exists NonceAppExpr not supported"
            W4.ArrayFromFn {} -> error "ArrayFromFn NonceAppExpr not supported"
            W4.MapOverArrays {} -> error "MapOverArrays NonceAppExpr not supported"
            W4.ArrayTrueOnEntries {} -> error "ArrayTrueOnEntries NonceAppExpr not supported"
        go (W4.BoundVarExpr var) = return $ convertBoundVarExpr var

-- | Serialize bound variables as the s-expression identifier `name_nonce`. This allows us to
-- preserve their human-readable name while ensuring they are globally unique w/ the nonce suffix.
convertBoundVarExpr :: forall t tp. W4.ExprBoundVar t tp -> SExp
convertBoundVarExpr x = ident $ (T.unpack (W4.solverSymbolAsText (W4.bvarName x))) ++ "_" ++ (show $ W4.bvarId x)



convertAppExpr' :: forall t tp . W4.AppExpr t tp -> Memo t SExp
convertAppExpr' = go . W4.appExprApp
  where go :: forall tp' . W4.App (W4.Expr t) tp' -> Memo t SExp
        go (W4.BaseIte _bt _ e1 e2 e3) = do
          s1 <- goE e1
          s2 <- goE e2
          s3 <- goE e3
          return $ S.L [ident "ite", s1, s2, s3]
        go (W4.BaseEq _bt e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "=", s1, s2]
        go (W4.NotPred e) = do
          s <- goE e
          return $ S.L [ident "notp", s]
        go (W4.ConjPred bm) = convertBoolMap "andp" True bm
        go (W4.DisjPred bm) = convertBoolMap "orp" False bm
        go (W4.BVSlt e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvslt", s1, s2]
        go (W4.BVUlt e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvult", s1, s2]
        go (W4.BVConcat _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "concat", s1, s2]
        go (W4.BVSelect idx n bv) = extract i j bv
          -- See SemMC.Formula.Parser.readExtract for the explanation behind
          -- these values.
          where i = intValue n + j - 1
                j = intValue idx

        -- Note that because the SemiRing has an identity element that
        -- always gets applied, resulting in lots of additional,
        -- unnecessary elements like: "(bvand #xffffffff TERM)".
        -- These will get manifested in the stored form (but generally
        -- _not_ via DSL-generated versions since they don't output
        -- via Printer) and result in longer stored forms.  They could
        -- be eliminated by checking for the identity (e.g. "if mul ==
        -- SR.one (WSum.sumRepr sm)") but the re-loaded representation
        -- will still use the SemiRing, so it's probably not worth the
        -- effort to reduce these.
        go (W4.SemiRingSum sm) =
          case WSum.sumRepr sm of
            W4.SemiRingBVRepr W4.BVArithRepr w ->
              let smul mul e = do
                    s <- goE e
                    return $ S.L [ ident "bvmul", bitvec (natValue w) mul, s]
                  sval v = return $ bitvec (natValue w) v
                  add x y = return $ S.L [ ident "bvadd", x, y ]
              in WSum.evalM add smul sval sm
            W4.SemiRingBVRepr W4.BVBitsRepr w ->
              let smul mul e = do
                    s <- goE e
                    return $ S.L [ ident "bvand", bitvec (natValue w) mul, s]
                  sval v = return $ bitvec (natValue w) v
                  add x y = let op = ident "bvxor" in return $ S.L [ op, x, y ]
              in WSum.evalM add smul sval sm
            W4.SemiRingNatRepr ->
              let smul mul e = do
                    s <- goE e
                    return $ S.L [ ident "natmul", nat mul, s]
                  sval v = return $ nat v
                  add x y = return $ S.L [ ident "natadd", x, y ]
              in WSum.evalM add smul sval sm
            W4.SemiRingIntegerRepr ->
              let smul mul e = do
                    s <- goE e
                    return $ S.L [ ident "intmul", int mul, s]
                  sval v = return $ int v
                  add x y = return $ S.L [ ident "intadd", x, y ]
              in WSum.evalM add smul sval sm
            W4.SemiRingRealRepr    -> error "SemiRingSum RealRepr not supported"

        go (W4.SemiRingProd pd) =
          case WSum.prodRepr pd of
            W4.SemiRingBVRepr W4.BVArithRepr w -> do
              let pmul x y = return $ S.L [ ident "bvmul", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ bitvec (natValue w) 1
            W4.SemiRingBVRepr W4.BVBitsRepr w -> do
              let pmul x y = return $ S.L [ ident "bvand", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ bitvec (natValue w) 1
            W4.SemiRingIntegerRepr -> do
              let pmul x y = return $ S.L [ ident "intmul", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ int 1
            W4.SemiRingNatRepr     -> error "convertApp W4.SemiRingProd Nat unsupported"
            W4.SemiRingRealRepr    -> error "convertApp W4.SemiRingProd Real unsupported"

        go (W4.SemiRingLe sr e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          case sr of
            W4.OrderedSemiRingIntegerRepr -> do
              return $ S.L [ ident "intle", s1, s2]
            W4.OrderedSemiRingNatRepr -> do
              return $ S.L [ ident "natle", s1, s2]
            W4.OrderedSemiRingRealRepr -> error $ "Printer: SemiRingLe is not supported for reals"

        go (W4.BVOrBits pd) =
          case WSum.prodRepr pd of
            W4.SemiRingBVRepr _ w -> do
              let pmul x y = return $ S.L [ ident "bvor", x, y ]
              maybeS <- WSum.prodEvalM pmul goE pd
              case maybeS of
                Just s -> return s
                Nothing -> return $ bitvec (natValue w) 0
        go (W4.BVUdiv _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvudiv", s1, s2]
        go (W4.BVUrem _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvurem", s1, s2]
        go (W4.BVSdiv _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvsdiv", s1, s2]
        go (W4.BVSrem _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvsrem", s1, s2]
        go (W4.BVShl _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvshl", s1, s2]
        go (W4.BVLshr _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvlshr", s1, s2]
        go (W4.BVAshr _ e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "bvashr", s1, s2]
        go (W4.BVZext r e) = extend "zero" (intValue r) e
        go (W4.BVSext r e) = extend "sign" (intValue r) e

        go (W4.BVToInteger e) = do
          s <- goE e
          return $ S.L [ident "bvToInteger", s]

        go (W4.SBVToInteger e) = do
          s <- goE e
          return $ S.L [ident "sbvToInteger", s]

        go (W4.IntDiv e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "intdiv", s1, s2]
        go (W4.IntMod e1 e2) = do
          s1 <- goE e1
          s2 <- goE e2
          return $ S.L [ident "intmod", s1, s2]
        go (W4.IntAbs e1) = do
          s1 <- goE e1
          return $ S.L [ident "intabs", s1]
        go (W4.IntegerToBV e wRepr)  = do
          s <- goE e
          return $ S.L [ident "integerToBV"
                        , int $ toInteger (natValue wRepr)
                        , s]

        go (W4.StructCtor _tps es) = do
          ss <- convertExprAssignment es
          return $ S.L [ident "struct", S.L ss]
        go (W4.StructField e ix _fieldTp) = do
          s <- goE e
          return $ S.L [ident "field"
                        , s
                        , int $ toInteger $ Ctx.indexVal ix
                        ]

        go (W4.UpdateArray _ _ e1 es e2) = do
          s1 <- goE e1
          ss <- convertExprAssignment es
          s2 <- goE e2
          case ss of
            [idx] -> return $ S.L [ ident "updateArray", s1, idx, s2]
            _ -> error $ "multidimensional arrays not supported"
        go (W4.SelectArray _ e es) = do
          s <- goE e
          ss <- convertExprAssignment es
          case ss of
            [idx] -> return $ S.L [ ident "select", s, idx]
            _ -> error $ "multidimensional arrays not supported"

        go app = error $ "unhandled App: " ++ show app


        -- -- -- -- Helper functions! -- -- -- --
        
        goE :: forall tp' . W4.Expr t tp' -> Memo t SExp
        goE = convertExpr

        extend :: forall w. String -> Integer -> W4.Expr t (BaseBVType w) -> Memo t SExp
        extend op r e = do
          let w = case W4.exprType e of BaseBVRepr len -> intValue len
              extension = r - w
          s <- goE e
          return $ S.L [ S.L [ ident "_", ident $ op <> "_extend", int extension ]
                        , s
                        ]

        extract :: forall tp'. Integer -> Integer -> W4.Expr t tp' -> Memo t SExp
        extract i j bv = do
          s <- goE bv
          return $ S.L [ S.L [ ident "_", ident "extract", int i, int j ]
                        , s
                        ]

        convertBoolMap :: String -> Bool -> BooM.BoolMap (W4.Expr t) -> Memo t SExp
        convertBoolMap op base bm =
          let strBase b = if b
                          then S.L [ident "=", bitvec 1 0, bitvec 1 0]  -- true
                          else S.L [ident "=", bitvec 1 0, bitvec 1 1]  -- false
              strNotBase = strBase . not
          in case BooM.viewBoolMap bm of
               BooM.BoolMapUnit -> return $ strBase base
               BooM.BoolMapDualUnit -> return $ strNotBase base
               BooM.BoolMapTerms ts ->
                 let onEach e r = do
                       s <- arg e
                       return $ S.L [ident op, s, r]
                     arg (t, BooM.Positive) = goE t
                     arg (t, BooM.Negative) = do
                       s <- goE t
                       return $ S.L [ident "notp", s]
                 in F.foldrM onEach (strBase base) ts


convertExprAssignment ::
  Ctx.Assignment (W4.Expr t) sh
  -> Memo t [SExp]
convertExprAssignment es =
  case es of
    Ctx.Empty -> return $ []
    es' Ctx.:> e -> do
      s <- convertExpr e
      ss <- convertExprAssignment es'
      return $ s:ss



convertFnApp ::
  W4.ExprSymFn t args ret
  -> Ctx.Assignment (W4.Expr t) args
  -> Memo t SExp
convertFnApp fn args
  | name == "undefined"
  , BaseBVRepr nr <- W4.fnReturnType fn = do
      let call = S.L [ ident "_", ident "call", string "uf.undefined" ]
      return $ S.L [ call, int (NR.intValue nr) ]
  | otherwise = do
    let call = S.L [ ident "_", ident "call", string (T.unpack $ fullname) ]
    ss <- convertExprAssignment args
    W.tell $ Map.singleton fullname (SomeSome fn)
    return $ S.L $ call:ss
  where
    fullname = prefix <> name
    name = W4.solverSymbolAsText (W4.symFnName fn)
    prefix = case W4.symFnInfo fn of
      W4.UninterpFnInfo _ _ -> "uf."
      W4.DefinedFnInfo _ _ _ -> "df."
      _ -> error ("Unsupported function: " ++ T.unpack name)

convertBaseType :: BaseTypeRepr tp
              -> SExp
convertBaseType tp = case tp of
  W4.BaseBoolRepr -> S.A (AIdent "Bool")
  W4.BaseNatRepr -> S.A (AIdent "Nat")
  W4.BaseIntegerRepr -> S.A (AIdent "Int")
  W4.BaseRealRepr -> S.A (AIdent "Real")
  W4.BaseStringRepr _ -> S.A (AIdent "String") -- parser assumes unicode
  W4.BaseComplexRepr -> S.A (AIdent "Complex")
  W4.BaseBVRepr wRepr -> S.L [S.A (AIdent "BV"), S.A (AInt (NR.intValue wRepr)) ]
  W4.BaseStructRepr tps -> S.L [S.A (AIdent "Struct"), convertBaseTypes tps]
  W4.BaseArrayRepr ixs repr -> S.L [S.A (AIdent "Array"), convertBaseTypes ixs , convertBaseType repr]
  _ -> error "can't print base type"

-- | Note `convertBaseTypes` does not "reverse" the list, but syntactically
-- the resulting list appears "reversed" because list-cons and Ctx-cons take
-- their arguments in opposite orders
convertBaseTypes ::
  Ctx.Assignment BaseTypeRepr tps
  -> SExp
convertBaseTypes = S.L . go
  where go :: Ctx.Assignment BaseTypeRepr tps -> [SExp]
        go Ctx.Empty = []
        go (tps Ctx.:> tp) = (convertBaseType tp):(go tps)

