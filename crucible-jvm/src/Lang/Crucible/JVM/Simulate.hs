{- |
Module           : Lang.Crucible.JVM.Simulate
Description      : Set up Crucible simulation of a JVM CFG
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : sweirich@galois.com
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -haddock #-}

module Lang.Crucible.JVM.Simulate where

-- base
import           Data.Maybe (maybeToList)
import           Data.Semigroup (Semigroup(..),(<>))
import           Control.Monad.State.Strict
import           Control.Monad.ST
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.String (fromString)
import           Data.List (isPrefixOf)

import           System.IO

-- jvm-parser
import qualified Language.JVM.Common as J
import qualified Language.JVM.Parser as J

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr as NR


-- crucible
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Backend

import           Lang.Crucible.Utils.MonadVerbosity

import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.RegValue as C (injectVariant)
import qualified Lang.Crucible.Analysis.Postdom as C
import qualified Lang.Crucible.Simulator.CallFrame as C


-- what4
import           What4.ProgramLoc (Position(InternalPos))
import           What4.FunctionName
import qualified What4.Interface as W4
import qualified What4.InterpretedFloatingPoint as W4
import qualified What4.Config as W4
import qualified What4.Partial as W4

import           What4.Utils.MonadST (liftST)

-- crucible-jvm
import           Lang.Crucible.JVM.Types
import           Lang.Crucible.JVM.Context
import           Lang.Crucible.JVM.Translation (translateMethod, jvmIntrinsicTypes, jvmExtensionImpl)
import           Lang.Crucible.JVM.ClassRefs
import           Lang.Crucible.JVM.Translation.Monad
import           Lang.Crucible.JVM.Translation.Class
import           Lang.Crucible.JVM.Overrides

import qualified Lang.JVM.Codebase as JCB


{-
   This module is in two parts, the first part includes functions for translating
   JVM code to Crucible CFGs.  The second part sets up the Crucible simulation
   itself.


   Here is how the simulator is set up in [executeCrucibleJVM]:

    - [findAllRefs] figures out which classes should be prepped
      for translation
        -- uses [initClasses] and [exclude] automatically include/exclude
           certain primitive classes
    - classes are then prepped via [extendJVMContext]
        -- allocate method handles (but do not yet translate methods)
        -- allocate global vars for static fields (but do not initialize them yet)
        -- add J.Class to Class table
    - [mkSimSt] creates the initial simulation state
        -- adds global variables
        -- installs overrides for all methods that translate them JIT
        -- adds additional overrides for primitives [stdOverrides]
    - [runMethodHandle] runs a method
        -- creates the simulation state
        -- installs overrides for primitives from the Java
           standard library classes
        -- invokes the method

-}

--------------------------------------------------------------------------------

-- * Special treatment of the Java standard library


{- Overall, the system doesn't take a very principled approach to classes from
   Java's standard library that are referred to in the test cases.

   The basic idea is that when we similate a Java method call, we first crawl
   over the enclosing class and declare its static vars and dynamic methods
   to the simulator. Because those classes could depend on others, we
   do this step transitively, declaring any class that could be needed.

   However, some of the classes that are implemented via native methods cannot
   be parsed by the jvm-parser code. So, those classes cannot be traversed to
   look for transitive mentions of other classes.

   In that case, we need to define a set of "initClasses", i.e.
   baseline primitives. These classes we declare only, but we make no
   guarantees that the classes that they refer to will also be
   available. Instead, we need to implement the *native* functionality
   from these classes via static or dynamic overrides.

-}

--------------------------------------------------------------------------------

-- * [findAllRefs] What classes should be prepped?

-- | Classes that are always loaded into the initial
-- environment.
-- THIS MUST INCLUDE ALL CLASSES in 'stdOverrides'.
-- (We could calculate automatically, but that would add an ambiguous
-- sym constraint to this definition, so we do not.)

initClasses :: [String]
initClasses =  [ "java/lang/Class"
               , "java/lang/String"
               , "java/io/BufferedOutputStream"
               , "java/io/FilterOutputStream"
               , "java/io/OutputStream"
               , "java/io/PrintStream"
               , "java/lang/Object"
               , "java/lang/System"
               , "java/lang/StringIndexOutOfBoundsException"
               , "java/lang/Exception"
               ]

-- These classes rely on native code that cannot be parsed by
-- jvm-parser. So instead of traversing these classes to find their
-- immediate dependencies, we list the ones that we care about
-- explicitly. (These dependencies do not need to include any of the
-- initClasses, which are always included.)
manualDependencies :: Map J.ClassName (Set.Set J.ClassName)
manualDependencies =
  Map.fromList $ map (\(s1,s2) -> (J.mkClassName s1, (Set.fromList (map J.mkClassName s2))))
  [ ("java/lang/Object",[])
  ,("java/lang/System", [])
  ,("java/lang/Class",[])
  ,("java/lang/String",
     ["java/lang/StringBuffer"
     ,"java/lang/AbstractStringBuilder"])
  ,("java/lang/StringBuffer",
     ["java/lang/AbstractStringBuilder"])
  ,("java/lang/AbstractStringBuilder",
     ["java/util/Arrays"
     ,"java/lang/IndexOutOfBoundsException"
     ,"java/lang/Integer"])
  ,("java/lang/StringBuilder", [])
  ,("java/util/Arrays",
     ["java/lang/IndexOutOfBoundsException"])
  ,("java/lang/Throwable", [])
  ,("java/util/Random",[])
  ,("java/math/BigInteger",[])
  ,("java/lang/StackTraceElement",[])

{-  -- DON'T need these anymore.
  ,("java/lang/Short", [])
  ,("java/lang/Byte", [])
  ,("java/lang/Long", [])
  ,("java/lang/Boolean", [])
  ,("java/lang/Character", [])
  ,("java/lang/Float", [])
  ,("java/lang/Double", [])
  ,("java/lang/Math", ["java/lang/StrictMath"])
  ,("java/lang/Number", [])
  ,("java/lang/Void", [])

  ,("sun/misc/FloatingDecimal", [])

  ,("java/io/FileOutputStream", [])
  ,("java/io/OutputStream", [])
  ,("java/io/ObjectStreamField", [])
  ,("java/io/FilterOutputStream", [])
  ,("java/io/File", [])
  ,("java/io/IOException", [])
  ,("java/io/DefaultFileSystem", [])



  ,("java/lang/Exception", ["java/lang/Throwable"])
  ,("java/lang/RuntimeException", ["java/lang/Exception"])
  ,("java/lang/NullPointerException", ["java/lang/Exception"])
  ,("java/lang/RuntimeException", ["java/lang/Exception"])
  ,("java/lang/IllegalArgumentException", ["java/lang/Exception"])
  ,("java/lang/IndexOutOfBoundsException", ["java/lang/Exception"])

  ,("java/lang/Error", ["java/lang/Throwable"])
  ,("java/lang/InternalError", ["java/lang/Error"])
  ,("java/lang/VirtualMachineError", ["java/lang/Error"])

  ,("java/lang/Thread", [])
  ,("java/lang/Runtime", [])  -}
  ]


-- | Class references that we shouldn't include in the transitive closure
--   of class references.
exclude :: J.ClassName -> Bool
exclude cn =
             ("java/nio/" `isPrefixOf` J.unClassName cn)
          || ("java/awt/" `isPrefixOf` J.unClassName cn)
          || ("java/io/" `isPrefixOf` J.unClassName cn)
          || ("java/time/" `isPrefixOf` J.unClassName cn)
          || ("sun/"       `isPrefixOf` J.unClassName cn)
          || ("java/security/" `isPrefixOf` J.unClassName cn)
          || ("java/text/"     `isPrefixOf` J.unClassName cn)
          || ("java/lang/reflect/"     `isPrefixOf` J.unClassName cn)
          || ("java/lang/ref/" `isPrefixOf` J.unClassName cn)
          || ("java/net/"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/System"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/Thread"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/CharSequence"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/ClassLoader"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/Character"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/ConditionalSpecialCasing"  `isPrefixOf` J.unClassName cn)
          || cn `elem` [
  -- cut off some packages that are rarely used and that we don't
  -- want to support
               J.mkClassName "java/lang/Package"
             , J.mkClassName "java/util/Formatter"
             , J.mkClassName "java/util/Locale"
             , J.mkClassName "java/lang/Runnable"
             , J.mkClassName "java/lang/SecurityManager"
             , J.mkClassName "java/lang/Shutdown"
             , J.mkClassName "java/lang/Process"
             , J.mkClassName "java/lang/RuntimePermission"
             , J.mkClassName "java/lang/ProcessEnvironment"
             , J.mkClassName "java/lang/ProcessBuilder"
             , J.mkClassName "java/lang/Thread"
             , J.mkClassName "java/lang/ThreadLocal"
             , J.mkClassName "java/lang/ApplicationShutdownHooks"
             , J.mkClassName "java/lang/invoke/SerializedLambda"
             , J.mkClassName "java/lang/System$2"
           ]



findNextRefs :: J.Class -> Set.Set J.ClassName
findNextRefs cls
  | Just refs <- Map.lookup (J.className cls) manualDependencies
  = refs
  | otherwise
  = classRefs cls

-- | Determine all other classes that need to be "prepped" in addition
-- to the current class.
findAllRefs :: IsCodebase cb => cb -> J.ClassName -> IO [ J.Class ]
findAllRefs cb cls = do
  names <- go Set.empty (Set.insert cls (Set.fromList (map J.mkClassName initClasses)))
  mapM (lookupClass cb) names
  where
    go :: Set.Set J.ClassName -> Set.Set J.ClassName -> IO [J.ClassName]
    go curr fringe = do
      (currClasses :: [J.Class]) <- traverse (lookupClass cb) (Set.toList fringe)
      let newRefs = fmap findNextRefs currClasses
      let permissable = Set.filter (not . exclude) (Set.unions newRefs)
      let newCurr   = fringe `Set.union` curr
      let newFringe = permissable `Set.difference` newCurr
      if Set.null newFringe
        then return (Set.toList newCurr)
        else go newCurr newFringe

-----------------------------------------------------------------------------
-- * Class Preparation [extendJVMContext]
--    + allocate method handles (but do not yet translate methods)
--    + allocate global vars for static fields (but do not initialize them yet)
--    + add the class to Class table

-- | Allocate a new method handle and add it to the table of method handles.
declareMethod :: HandleAllocator s
              -> J.Class
              -> MethodHandleTable
              -> J.Method
              -> ST s MethodHandleTable
declareMethod halloc mcls ctx meth =
  let cname    = J.className mcls
      mkey     = J.methodKey meth
  in do
   jvmToFunHandleRepr (J.methodIsStatic meth) mkey $
      \ argsRepr retRepr -> do
         --traceM $ "declaring " ++ J.unClassName cname ++ "/" ++ J.methodName meth
         --           ++ " : " ++ showJVMArgs argsRepr ++ " ---> " ++ showJVMType retRepr
         h <- mkHandle' halloc (methodHandleName cname mkey) argsRepr retRepr
         return $ Map.insert (cname, mkey) (JVMHandleInfo mkey h) ctx

-- | Allocate the static field (a global variable)
-- and add it to the static field table.
declareStaticField :: HandleAllocator s
    -> J.Class
    -> StaticFieldTable
    -> J.Field
    -> ST s StaticFieldTable
declareStaticField halloc c m f = do
  let cn = J.className c
  let fn = J.fieldName f
  let fieldId = J.FieldId cn fn (J.fieldType f)
  let str = fn ++ show (J.fieldType f)
  gvar <- C.freshGlobalVar halloc (globalVarName cn str) (knownRepr :: TypeRepr JVMValueType)
  return $ (Map.insert (cn,fieldId) gvar m)


-- | Create the initial 'JVMContext'.
mkInitialJVMContext :: HandleAllocator RealWorld -> IO JVMContext
mkInitialJVMContext halloc = do

  gv <- stToIO $ C.freshGlobalVar halloc (fromString "JVM_CLASS_TABLE")
                                (knownRepr :: TypeRepr JVMClassTableType)

  return (JVMContext
              { methodHandles     = Map.empty
              , staticFields      = Map.empty
              , classTable        = Map.empty
              , dynamicClassTable = gv
              })

-- | Extend the JVM context in preparation for translating class @c@
-- by declaring handles for all methods,
--    declaring global variables for all static fields, and
--    adding the class information to the class table.
extendJVMContext :: HandleAllocator s -> J.Class -> StateT JVMContext (ST s) ()
extendJVMContext halloc c = do
  sm <- lift $ foldM (declareMethod halloc c) Map.empty (J.classMethods c)
  st <- lift $ foldM (declareStaticField halloc c) Map.empty (J.classFields c)
  modify $ \ctx0 -> JVMContext
    { methodHandles     = sm
    , staticFields      = st
    , classTable        = Map.singleton (J.className c) c
    , dynamicClassTable = dynamicClassTable ctx0
    } <> ctx0

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Simulation
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


-- * make the simulation state & run a method

-- | Make a binding for a Java method that, when invoked, immediately
-- translates the Java source code and then runs it.
mkDelayedBinding :: forall p sym .
                    JVMContext
                 -> Verbosity
                 -> J.Class
                 -> J.Method
                 -> JVMHandleInfo
                 -> C.FnBinding p sym JVM
mkDelayedBinding ctx verbosity c m (JVMHandleInfo _mk (handle :: FnHandle args ret))
  = let cm           = J.unClassName (J.className c) ++ "/" ++ J.methodName m
        fn           = functionNameFromText (fromString (J.methodName m))
        retRepr      = handleReturnType handle

        overrideSim :: C.OverrideSim p sym JVM r args ret (C.RegValue sym ret)
        overrideSim  = do whenVerbosity (> 3) $
                            do liftIO $ putStrLn $ "translating (delayed) "
                                 ++ cm ++ " with args " ++ show (J.methodParameterTypes m) ++ "\n"
                                 ++ "and body " ++
                                     show (J.methodBody m)
                          args <- C.getOverrideArgs
                          C.SomeCFG cfg <- liftST $ translateMethod ctx
                                                       verbosity (J.className c) m handle
                          C.bindFnHandle handle (C.UseCFG cfg (C.postdomInfo cfg))
                          (C.RegEntry _tp regval) <- C.callFnVal (C.HandleFnVal handle) args
                          return regval
    in
      C.FnBinding handle (C.UseOverride (C.mkOverride' fn retRepr overrideSim))

-- | Make bindings for all methods in the 'JVMContext' classTable that have
-- associated method handles.
mkDelayedBindings :: forall p sym . JVMContext -> Verbosity -> C.FunctionBindings p sym JVM
mkDelayedBindings ctx verbosity =
  let bindings = [ mkDelayedBinding ctx verbosity c m h | (cn,c) <- Map.assocs (classTable ctx)
                                              , m <- J.classMethods c
                                              , h <- maybeToList $ Map.lookup (cn,J.methodKey m)
                                                     (methodHandles ctx)
                                              ]
  in
    C.fnBindingsFromList bindings


-- | Make the initial state for the simulator, binding the function handles so that
-- they translate method bodies when they are accessed.
mkSimSt ::
  -- forall sym .
  (IsSymInterface sym) =>
  sym ->
  p ->
  HandleAllocator RealWorld ->
  JVMContext ->
  Verbosity ->
  C.ExecCont p sym JVM (C.RegEntry sym ret) (C.OverrideLang ret) ('Just EmptyCtx) ->
  IO (C.ExecState p sym JVM (C.RegEntry sym ret))
mkSimSt sym p halloc ctx verbosity k =
  do globals <- Map.foldrWithKey initField (return globals0) (staticFields ctx)
     return $ C.InitialState simctx globals C.defaultAbortHandler k
  where
    -- initField :: (J.ClassName, J.FieldId) -> GlobalVar JVMValueType -> IO (C.SymGlobalState sym) -> IO (C.SymGlobalState sym)
    initField (_, fi) var m =
      do gs <- m
         z <- zeroValue sym (J.fieldIdType fi)
         return (C.insertGlobal var z gs)

    simctx = C.initSimContext sym
               jvmIntrinsicTypes
               halloc
               stdout
               (mkDelayedBindings ctx verbosity)
               jvmExtensionImpl
               p
    globals0 = C.insertGlobal (dynamicClassTable ctx) Map.empty C.emptyGlobals

-- | Construct a zero value of the appropriate type. This is used for
-- initializing static fields of classes.
zeroValue :: IsSymInterface sym => sym -> J.Type -> IO (C.RegValue sym JVMValueType)
zeroValue sym ty =
  case ty of
    J.ArrayType _ -> C.injectVariant sym knownRepr tagR <$> return W4.Unassigned
    J.BooleanType -> C.injectVariant sym knownRepr tagI <$> W4.bvLit sym w32 0
    J.ByteType    -> C.injectVariant sym knownRepr tagI <$> W4.bvLit sym w32 0
    J.CharType    -> C.injectVariant sym knownRepr tagI <$> W4.bvLit sym w32 0
    J.ClassType _ -> C.injectVariant sym knownRepr tagR <$> return W4.Unassigned
    J.DoubleType  -> C.injectVariant sym knownRepr tagD <$> W4.iFloatPZero sym DoubleFloatRepr
    J.FloatType   -> C.injectVariant sym knownRepr tagF <$> W4.iFloatPZero sym SingleFloatRepr
    J.IntType     -> C.injectVariant sym knownRepr tagI <$> W4.bvLit sym w32 0
    J.LongType    -> C.injectVariant sym knownRepr tagL <$> W4.bvLit sym w64 0
    J.ShortType   -> C.injectVariant sym knownRepr tagI <$> W4.bvLit sym w32 0

-- (currently unused)
-- Way to run initialization code before simulation starts
-- Currently this code initializes the current class
runClassInit :: HandleAllocator RealWorld -> JVMContext -> Verbosity -> J.ClassName
             -> C.OverrideSim p sym JVM rtp a r (C.RegEntry sym C.UnitType)
runClassInit halloc ctx verbosity name = do
  (C.SomeCFG g') <- liftIO $ stToIO $ do
      h <- mkHandle halloc (fromString ("class_init:" ++ J.unClassName name))
      let (meth :: J.Method) = undefined
          def :: FunctionDef JVM s (JVMState UnitType) EmptyCtx UnitType
          def _inputs = (s, f)
              where s = initialState ctx verbosity meth knownRepr
                    f = do () <- initializeClass name
                           return (App EmptyApp)
      (SomeCFG g, []) <- defineFunction InternalPos h def
      return (toSSA g)
  C.callCFG g' (C.RegMap Ctx.Empty)



-- | Install the standard overrides and run a Java method in the simulator.
runMethodHandleCrux
  :: IsSymInterface sym
  => [C.GenericExecutionFeature sym]
  -> sym
  -> p
  -> HandleAllocator RealWorld
  -> JVMContext
  -> Verbosity
  -> J.ClassName
  -> FnHandle args ret
  -> C.RegMap sym args
  -> IO (C.ExecResult p sym JVM (C.RegEntry sym ret))
runMethodHandleCrux feats sym p halloc ctx verbosity _classname h args = do
  let fnCall = C.regValue <$> C.callFnVal (C.HandleFnVal h) args
  let overrideSim = do _ <- runStateT (mapM_ register_jvm_override stdOverrides) ctx
                       -- _ <- runClassInit halloc ctx classname
                       fnCall
  simSt <- mkSimSt sym p halloc ctx verbosity (C.runOverrideSim (handleReturnType h) overrideSim)
  C.executeCrucible (map C.genericToExecutionFeature feats) simSt


runMethodHandle
  :: IsSymInterface sym
  => sym
  -> p
  -> HandleAllocator RealWorld
  -> JVMContext
  -> Verbosity
  -> J.ClassName
  -> FnHandle args ret
  -> C.RegMap sym args
  -> IO (C.ExecResult p sym JVM (C.RegEntry sym ret))

runMethodHandle = runMethodHandleCrux []

--------------------------------------------------------------------------------

-- * Top-level entry point [executeCrucibleJVM]


findMethodHandle :: JVMContext -> J.Class -> J.Method -> IO JVMHandleInfo
findMethodHandle ctx cls meth =
    case  Map.lookup (J.className cls, J.methodKey meth) (methodHandles ctx) of
        Just handle ->
          return handle
        Nothing ->
          fail $ "BUG: cannot find handle for " ++ J.unClassName (J.className cls)
               ++ "/" ++ J.methodName meth

setSimulatorVerbosity :: (W4.IsSymExprBuilder sym) => Int -> sym -> IO ()
setSimulatorVerbosity verbosity sym = do
  verbSetting <- W4.getOptionSetting W4.verbosity (W4.getConfiguration sym)
  _ <- W4.setOpt verbSetting (toInteger verbosity)
  return ()

-- | Read from the provided java code base and simulate a
-- given static method.
--
--    Set the verbosity level for simulation
--    Find the class/method information from the codebase
--    Set up handles for java.lang.* & primitives
--    declare the handle for all methods in this class
--    Find the handle for this method
--    run the simulator given the handle

type ExecuteCrucible sym = (forall p ext rtp f a0.
     IsSyntaxExtension ext =>
      C.SimState p sym ext rtp f a0  ->
      C.ExecCont p sym ext rtp f a0  ->
      IO (C.ExecResult p sym ext rtp))


executeCrucibleJVMCrux
  :: forall ret args sym p cb
   . (IsSymInterface sym, KnownRepr CtxRepr args, KnownRepr TypeRepr ret, IsCodebase cb)
  => [C.GenericExecutionFeature sym]
  -> cb
  -> Int               -- ^ Verbosity level
  -> sym               -- ^ Simulator state
  -> p                 -- ^ Personality
  -> String            -- ^ Dot-separated class name
  -> String            -- ^ Method name
  -> C.RegMap sym args -- ^ Arguments
  -> IO (C.ExecResult p sym JVM (C.RegEntry sym ret))
executeCrucibleJVMCrux feats cb verbosity sym p cname mname args = do

     when (verbosity > 2) $
       putStrLn "starting executeCrucibleJVM"

     setSimulatorVerbosity verbosity sym

     (mcls, meth) <- findMethod cb mname =<< findClass cb cname
     when (not (J.methodIsStatic meth)) $ do
       fail $ unlines [ "Crucible can only extract static methods" ]

     halloc <- newHandleAllocator

     -- Create the initial JVMContext
     ctx0 <- mkInitialJVMContext halloc

     -- prep this class && all classes that it refers to
     allClasses <- findAllRefs cb (J.className mcls)
     when (verbosity > 3) $
       putStrLn $ "all classes are: " ++ show (map J.className allClasses)
     ctx <- stToIO $ execStateT (extendJVMContext halloc mcls >>
                                 mapM (extendJVMContext halloc) allClasses) ctx0


     (JVMHandleInfo _ h) <- findMethodHandle ctx mcls meth


     let failIfNotEqual :: forall f m a (b :: k).
                           (Monad m, Show (f a), Show (f b), TestEquality f)
                        => f a -> f b -> String -> m (a :~: b)
         failIfNotEqual r1 r2 str
           | Just Refl <- testEquality r1 r2 = return Refl
           | otherwise = fail $ str ++ ": mismatch between " ++ show r1 ++ " and " ++ show r2
     Refl <- failIfNotEqual (handleArgTypes h)   (knownRepr :: CtxRepr args)
       $ "Checking args for method " ++ mname
     Refl <- failIfNotEqual (handleReturnType h) (knownRepr :: TypeRepr ret)
       $ "Checking return type for method " ++ mname

     runMethodHandleCrux feats sym p halloc ctx verbosity (J.className mcls) h args


executeCrucibleJVM
  :: forall ret args sym p cb
   . (IsSymInterface sym, KnownRepr CtxRepr args, KnownRepr TypeRepr ret, IsCodebase cb)
  => cb
  -> Int               -- ^ Verbosity level
  -> sym               -- ^ Simulator state
  -> p                 -- ^ Personality
  -> String            -- ^ Dot-separated class name
  -> String            -- ^ Method name
  -> C.RegMap sym args -- ^ Arguments
  -> IO (C.ExecResult p sym JVM (C.RegEntry sym ret))
executeCrucibleJVM = executeCrucibleJVMCrux []


getGlobalPair ::
  C.PartialResult sym ext v ->
  IO (C.GlobalPair sym v)
getGlobalPair pr =
  case pr of
    C.TotalRes gp -> return gp
    C.PartialRes _ gp _ -> do
      putStrLn "Symbolic simulation completed with side conditions."
      return gp

--------------------------------------------------------------------------------


-- | A type class for what we need from a Java code base.
-- This is here b/c we have two copies of the Codebase module, the one in this
-- package and the one in the jvm-verifier package. Eventually,
-- saw-script will want to transition to the code base in this package,
-- but it will need to eliminate uses of the old jvm-verifier first.
class IsCodebase cb where

   lookupClass :: cb -> J.ClassName -> IO J.Class

   findMethod :: cb -> String -> J.Class -> IO (J.Class,J.Method)

   findClass  :: cb -> String {- ^ Dot-separated class name -} -> IO J.Class
   findClass cb cname = (lookupClass cb . J.mkClassName . J.dotsToSlashes) cname

------------------------------------------------------------------------
-- * utility operations for working with the java code base
-- Some of these are from saw-script util

instance IsCodebase JCB.Codebase where

   lookupClass = cbLookupClass

   -- | Returns method with given name in this class or one of its subclasses.
   -- Throws an 'ExecException' if method could not be found or is ambiguous.
   -- findMethod :: JCB.Codebase -> String -> J.Class -> IO (J.Class, J.Method)
   findMethod cb nm initClass = impl initClass
    where javaClassName = J.slashesToDots (J.unClassName (J.className initClass))
          methodMatches m = J.methodName m == nm && not (J.methodIsAbstract m)
          impl cl =
            case filter methodMatches (J.classMethods cl) of
              [] -> do
                case J.superClass cl of
                  Nothing ->
                    let msg =  "Could not find method " ++ nm
                                ++ " in class " ++ javaClassName ++ "."
                        res = "Please check that the class and method are correct."
                     in throwIOExecException msg res
                  Just superName ->
                    impl =<< cbLookupClass cb superName
              [method] -> return (cl,method)
              _ -> let msg = "The method " ++ nm ++ " in class " ++ javaClassName
                               ++ " is ambiguous.  SAWScript currently requires that "
                               ++ "method names are unique."
                       res = "Please rename the Java method so that it is unique."
                    in throwIOExecException msg res


-- | Attempt to find class with given name, or throw 'ExecException' if no class
-- with that name exists. Class name should be in slash-separated form.
cbLookupClass :: JCB.Codebase -> J.ClassName -> IO J.Class
cbLookupClass cb nm = do
  maybeCl <- JCB.tryLookupClass cb nm
  case maybeCl of
    Nothing -> do
     let msg = ("The Java class " ++ J.slashesToDots
                       (J.unClassName nm) ++ " could not be found.")
         res = "Please check that the --classpath and --jars options are set correctly."
      in throwIOExecException msg res
    Just cl -> return cl



throwFieldNotFound :: J.Type -> String -> IO a
throwFieldNotFound tp fieldName = throwE msg
  where
    msg = "Values with type \'" ++ show tp ++
          "\' do not contain field named " ++
          fieldName ++ "."

-- | Throw exec exception in a MonadIO.
throwIOExecException :: String -> String -> IO a
throwIOExecException errorMsg resolution = liftIO $ throwE $ errorMsg ++ "\n" ++ resolution


findField :: JCB.Codebase -> J.Type -> String -> IO J.FieldId
findField _  tp@(J.ArrayType _) nm = throwFieldNotFound tp nm
findField cb tp@(J.ClassType clName) nm = impl =<< (cbLookupClass cb clName)
  where
    impl cl =
      case filter (\f -> J.fieldName f == nm) $ J.classFields cl of
        [] -> do
          case J.superClass cl of
            Nothing -> throwFieldNotFound tp nm
            Just superName -> impl =<< (cbLookupClass cb  superName)
        [f] -> return $ J.FieldId (J.className cl) nm (J.fieldType f)
        _ -> throwE $
             "internal: Found multiple fields with the same name: " ++ nm
findField  _ _ _ =
  throwE "Primitive types cannot be dereferenced."


throwE :: String -> IO a
throwE = fail