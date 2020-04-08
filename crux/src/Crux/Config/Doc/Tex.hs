module Crux.Config.Doc.Tex
  ( configTexDocs
  , TexDocs(..)
  , TexConfig(..)
  , defaultTexConfig
  ) where

import           Text.PrettyPrint ( Doc )
import qualified Text.PrettyPrint as PP
import           Config.Schema(sectionsSpec,generateDocs)
import           SimpleGetOpt( usageString, OptSpec(..), OptDescr(..))
import           Data.List (intersperse, intercalate)

import           Data.String ( IsString(..) )
import           Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map


import Data.List (intersperse, intercalate)


import           Control.Monad.Reader ( ReaderT )
import qualified Control.Monad.Reader as MR
import           Control.Monad.State.Strict ( State )
import qualified Control.Monad.State.Strict as MS


import Crux.Config
import Crux.Config.Load(commandLineOptions)


-- | A monad to track generated TeX macros so we can:
--
--   * ensure we keep macro argument counts consistent, and
--
--   * generate empty and/or default definitions for the generated
--     macros so people have a simple `TODO` list (so to speak)
--     to get their TeX ready to compile.
type TexGen a = ReaderT TexConfig (State TexState) a

data TexConfig = TexConfig { cfgMacroNamePrefix :: String
                           -- ^ The prefix to use for generated TeX macros.
                           , cfgShortFlagFormatter :: String -> String
                           , cfgLongFlagFormatter :: String -> String
                           , cfgShortFlagDelimeter :: String
                           , cfgLongFlagDelimeter :: String
                           }

defaultTexConfig :: TexConfig
defaultTexConfig = TexConfig
  { cfgMacroNamePrefix = "Crux"
  , cfgShortFlagFormatter = ("-"++)
  , cfgLongFlagFormatter = ("--"++)
  , cfgShortFlagDelimeter = ", "
  , cfgLongFlagDelimeter = ", "
  }


data TexState =
  TexState { tsMacroArgSigs :: (Map String [ArgDescription])
             -- ^ Map from macro name to it's signature
             -- (i.e., the description of it's arguments).
           }

initTexState :: TexState
initTexState = TexState { tsMacroArgSigs = Map.empty }

data TexDocs = TexDocs
  { generatedDocs :: Doc
    -- ^ The generated output that has all of the
    -- specifics/details for the tool in question. N.B., to
    -- build the TeX the referenced macros in there must be
    -- actually defined somewhere ().
  , generatedMacroStubs :: Doc
  -- ^ During documentation generation, certain macros will
  -- be used to describe the various
  -- options/configurations/etc. This document contains
  -- "stub" TeX for those macros, which could be useful when
  -- generating TeX for the first time for a tool.
  }

-- | Generates TeX documation for the given Crux
-- configuration.
configTexDocs :: String -> TexConfig -> Config opts -> TexDocs 
configTexDocs toolName texCfg cruxCfg =
  TexDocs { generatedDocs =  unTex doc
          , generatedMacroStubs = macroStubs
          }
  where (doc, texState) = MS.runState (MR.runReaderT (configTexDocs' toolName cruxCfg) texCfg) initTexState
                          
        macroStubs = PP.vcat
                     $ map (uncurry texNewCmdStub)
                     $ Map.toList
                     $ tsMacroArgSigs texState

configTexDocs' :: String -> Config opts -> TexGen Tex
configTexDocs' toolName cruxCfg = cmdLineDocs toolName cruxCfg

cmdLineDocs :: String -> Config opts -> TexGen Tex
cmdLineDocs toolName cruxCfg = texOptSec $ commandLineOptions cruxCfg


texOptSec :: OptSpec a -> TexGen Tex
texOptSec OptSpec
  { progParamDocs = args -- [(String,String)] the positional args passed to the program
  , progOptions   = opts -- [OptDescr a] I.e., the actual options and command-line flags
  } = do
  args' <- mapM texArg args
  opts' <- mapM texOptDescr opts
  prefix <- MR.reader cfgMacroNamePrefix
  let cmdlineArgs = formatNewCommand (prefix++"CmdLineArgs") args'
      cmdlineOpts = formatNewCommand (prefix++"CmdLineOpts") opts'
  return $ tvapp [ Tex cmdlineArgs
                 , Tex cmdlineOpts
                 ]
    -- N.B., we take care to keep the newlines/whitespace fairly straightforward/simple
    -- (i.e., we manually choose more than one might otherwise with a pretty printer)
    -- so the TeX output is more predictable and less likely to have any issues.
    where formatNewCommand name [] = PP.text $ "\\newcommand{"++name++"}{}"
          formatNewCommand name [x] =
            PP.hcat $ [ PP.text $ "\\newcommand{"++name++"}{"
                      , unTex x
                      , PP.text "}"
                      ]
          formatNewCommand name (first:rest) =
            PP.vcat [ PP.hcat [PP.text $ "\\newcommand{"++name++"}{", unTex first]
                    , PP.hcat [PP.vcat (map unTex rest), PP.text "}"]
                    ]


-- | Generate TeX for a positional command line argument and it's description,
-- i.e. `\CruxCmdLineArg{arg name}{arg description}`
texArg :: (String,String) -> TexGen Tex
texArg (argName, argDescr) = cmdLineMacro "Arg" [ mk argName "Argument Name"
                                                , mk argDescr "Argument Description"
                                                ]
  where mk str descr = MacroArg (traw str) $ ArgDescription descr


-- | Generate TeX for a command line option  and it's description,
-- i.e. `\CruxCmdLineOpt{short flags}{long flags}{description}{argument?}`
texOptDescr :: OptDescr a -> TexGen Tex
texOptDescr Option
  { optShortFlags = rawShortFlags
  , optLongFlags = rawLongFlags
  , optDescription = descr
  , optArgument = argDescr
  } = do
  TexConfig { cfgShortFlagFormatter = sFn
            , cfgLongFlagFormatter = lFn
            , cfgShortFlagDelimeter = sDelim
            , cfgLongFlagDelimeter = lDelim
            } <- MR.ask
  let sArg flags = MacroArg (traw flags) $ ArgDescription "Option Short Flag(s)"
      lArg flags = MacroArg (traw flags) $ ArgDescription "Option Long Flag(s)"
      dOpt descr = MacroArg (traw descr) $ ArgDescription "Option Description"
      dArg descr = MacroArg (traw descr) $ ArgDescription "Option Argument Description"
      opt name args = cmdLineMacro ("Opt"++name) args
  case ( intercalate sDelim $ map (\c -> sFn [c]) rawShortFlags
       , intercalate lDelim $ map lFn rawLongFlags
       , argDescr
       ) of
    ([],     [],      _) -> error
                            $ "PANIC! Encountered an option with no short"
                            ++ " or long flags while generating TeX for Crux options." 
    ([],     lflags, (NoArg _))           -> opt "NoShortNoArg"  [lArg lflags, dOpt descr]
    ([],     lflags, (ReqArg argDescr _)) -> opt "NoShortReqArg" [lArg lflags, dOpt descr, dArg argDescr]
    ([],     lflags, (OptArg argDescr _)) -> opt "NoShortOptArg" [lArg lflags, dOpt descr, dArg argDescr]
    (sflags, [],     (NoArg _))           -> opt "NoLongNoArg"   [sArg sflags, dOpt descr]
    (sflags, [],     (ReqArg argDescr _)) -> opt "NoLongReqArg"  [sArg sflags, dOpt descr, dArg argDescr]
    (sflags, [],     (OptArg argDescr _)) -> opt "NoLongOptArg"  [sArg sflags, dOpt descr, dArg argDescr]
    (sflags, lflags, (NoArg _))           -> opt "NoArg"          [sArg sflags, lArg lflags, dOpt descr]
    (sflags, lflags, (ReqArg argDescr _)) -> opt "ReqArg"         [sArg sflags, lArg lflags, dOpt descr, dArg argDescr]
    (sflags, lflags, (OptArg argDescr _)) -> opt "OptArg"         [sArg sflags, lArg lflags, dOpt descr, dArg argDescr]


-- | Generates a TeX command that defines a new macro --
-- useful for generating default/stub implementations of
-- encountered macros.
texNewCmdStub :: String -> [ArgDescription] -> Doc
texNewCmdStub cmdName args = PP.vcat $ maybeArgDescriptionsComment ++ newcommand
  where argCount = length args
        newcommand = [PP.text $ "\\newcommand{"++cmdName++"}"++maybeArgCount++"{ TODO }"]
        (maybeArgDescriptionsComment, maybeArgCount) =
          if argCount == 0
          then ([], "")
          else ( [PP.text $ "% \\"++cmdName++(concatMap (\arg -> "{"++(argDescrStr arg)++"}") args)]
               , "["++show argCount++"]"
               )


-- | Generates a call to a macro whose name has the prefix @"CmdLine"@
cmdLineMacro :: String -> [MacroArg] -> TexGen Tex
cmdLineMacro nameSuffix args = tmacro ("CmdLine"++nameSuffix) args

-- | Wraps a `Doc` so we can be careful to only introduce
-- macro calls in places were were tracking the global state
-- for consistency.
newtype Tex = Tex {unTex :: Doc}

-- | Append Tex elements vertically.
tvapp :: [Tex] -> Tex
tvapp elems = Tex $ PP.vcat $ map unTex elems

-- | Turn the raw string into Tex -- NOTE! This shouldn't be
-- used for non-trivial content macro-calls etc, as it
-- circumvents our macro usage/arg count/etc checking.
traw :: String -> Tex
traw str = Tex $ PP.text str

-- | Describes an argument to a TeX macro and contains a
-- string description that will be used in stub definitions.
data MacroArg = MacroArg { macroArg :: Tex
                         , macroArgDescription :: ArgDescription
                         }

newtype ArgDescription = ArgDescription { argDescrStr :: String }
  deriving (Eq, Ord, Show)


-- | Generates a call to a macro with the given name and
-- args (if any), and checks that any previous usage of this
-- macro had the same number of args and the same.
tmacro :: String -> [MacroArg] -> TexGen Tex
tmacro nm args = do
  prefix <- MR.reader cfgMacroNamePrefix
  let macroName = prefix++nm
      macroArgs = map macroArgDescription args
      t = case args of
              [] -> Tex $ PP.text $ "\\"++macroName++"{}"
              _ -> Tex
                   $ PP.hcat
                   $ (PP.text $ "\\"++macroName)
                   : concatMap (\arg -> [PP.text "{", unTex $ macroArg arg, PP.text "}"]) args
      -- N.B. you can omit the `{}` in Tex for a macro that takes
      -- no args sometimes... other times it causes issues, so
      -- we do it in the no arg case to be safe.
  macroSigTable <- MS.gets tsMacroArgSigs
  case Map.lookup macroName macroSigTable of
    Nothing -> do
      MS.modify (\s -> s {tsMacroArgSigs = Map.insert macroName macroArgs macroSigTable})
      return t
    Just macroArgs'
      | macroArgs == macroArgs' -> return t
      | otherwise -> error $
                     "PANIC! While generating Crux TeX docs, the macro "
                     ++ macroName
                     ++ " was described as having two different argument sequences:\n  "
                     ++ show macroArgs
                     ++ "\nand\n  "
                     ++ show macroArgs'
  

