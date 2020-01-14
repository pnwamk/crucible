-- | Definition of the S-Expression tokens used to
-- (de)serialize What4 expressions.

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module What4.Serialize.SETokens
    ( Atom(..)
    , string, ident, int, bitvec, bool, nat, real
    , printAtom
    , printSExpr
    , parseSExpr
    )
    where

import qualified Data.Foldable as F
import qualified Data.SCargot as SC
import qualified Data.SCargot.Comments as SC
import qualified Data.SCargot.Repr as SC
import qualified Data.SCargot.Repr.WellFormed as SC
import           Data.Semigroup
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import           Numeric.Natural ( Natural )
import qualified Text.Parsec as P
import           Text.Parsec.Text ( Parser )
import           Text.Printf ( printf )
import           Data.Ratio

import           Prelude

data Atom = AIdent String
           | AString String
           | AInt Integer
           | ANat Natural
           | AReal Rational
           | ABV Int Integer
           | ABool Bool
           deriving (Show, Eq, Ord)

type SExpr = SC.WellFormedSExpr Atom

string :: String -> SExpr
string = SC.A . AString

-- | Lift an unquoted identifier.
ident :: String -> SExpr
ident = SC.A . AIdent

-- | Lift a quoted identifier.
-- quoted :: String -> SExpr
-- quoted = SC.A . AQuoted

-- | Lift an integer.
int :: Integer -> SExpr
int = SC.A . AInt

-- | Lift an integer.
nat :: Natural -> SExpr
nat = SC.A . ANat

-- | Lift an integer.
real :: Rational -> SExpr
real = SC.A . AReal


-- | Lift a bitvector.
bitvec :: Natural -> Integer -> SExpr
bitvec w v = SC.A $ ABV (fromEnum w) v

-- | Lift a boolean.
bool :: Bool -> SExpr
bool = SC.A . ABool


-- * Output of the S-Expression Formula language


-- | Generates the the S-expression tokens represented by the sexpr
-- argument, preceeded by a list of strings output as comments.
printSExpr :: Seq.Seq String -> SExpr -> T.Text
printSExpr comments sexpr =
  let outputFmt = SC.setIndentAmount 1 $ SC.unconstrainedPrint printAtom
  in formatComment comments <> (SC.encodeOne outputFmt $ SC.fromWellFormed sexpr)


formatComment :: Seq.Seq String -> T.Text
formatComment c
  | Seq.null c = T.empty
  | otherwise = T.pack $ unlines $ fmap formatLine (F.toList c)
  where
    formatLine l = printf ";; %s" l


printAtom :: Atom -> T.Text
printAtom a =
  case a of
    AIdent s -> T.pack s
    --AQuoted s -> T.pack ('\'' : s)
    AString s -> T.pack (show s)
    AInt i -> T.pack (show i)
    ANat n -> T.pack $ (show n)++"u"
    AReal r -> T.pack $ (show (numerator r))++"/"++(show (denominator r))
    ABV w val -> formatBV w val
    ABool b -> if b then "#true" else "#false"


formatBV :: Int -> Integer -> T.Text
formatBV w val = T.pack (prefix ++ printf fmt val)
  where
    (prefix, fmt)
      | w `rem` 4 == 0 = ("#x", "%0" ++ show (w `div` 4) ++ "x")
      | otherwise = ("#b", "%0" ++ show w ++ "b")


-- * Input and parse of the S-Expression Formula language

-- | This is only the base-level parsing of atoms.  The full language
-- parsing is handled by the base here and the Parser definitions.

parseIdent :: Parser String
parseIdent = (:) <$> first <*> P.many rest
  where first = P.letter P.<|> P.oneOf "@+-=<>_."
        rest = P.letter P.<|> P.digit P.<|> P.oneOf "+-=<>_."

parseString :: Parser String
parseString = do
  _ <- P.char '"'
  s <- P.many (P.noneOf ['"'])
  _ <- P.char '"'
  return s

parseBV :: Parser (Int, Integer)
parseBV = P.char '#' >> ((P.char 'b' >> parseBin) P.<|> (P.char 'x' >> parseHex))
  where parseBin = P.oneOf "10" >>= \d -> parseBin' (1, if d == '1' then 1 else 0)

        parseBin' :: (Int, Integer) -> Parser (Int, Integer)
        parseBin' (bits, x) = do
          P.optionMaybe (P.oneOf "10") >>= \case
            Just d -> parseBin' (bits + 1, x * 2 + (if d == '1' then 1 else 0))
            Nothing -> return (bits, x)

        parseHex = (\s -> (length s * 4, read ("0x" ++ s))) <$> P.many1 P.hexDigit

parseAtom :: Parser Atom
parseAtom
  =     ANat . read <$> P.try (P.many1 P.digit <* P.char 'u')
  -- P.<|> AReal . read <$> P.try (P.many1 P.digit <* P.char 'r') -- TODO parse `X/Y` as a real
  P.<|> AInt . read <$> P.many1 P.digit
  P.<|> AInt . (*(-1)) . read <$> (P.char '-' >> P.many1 P.digit)
  P.<|> AIdent      <$> parseIdent
  --P.<|> AQuoted     <$> (P.char '\'' >> parseIdent)
  P.<|> AString     <$> parseString
  P.<|> ABool       <$> P.try (P.try (P.string "#false" *> return False)
                               P.<|>
                               (P.string "#true" *> return True))
  P.<|> uncurry ABV <$> parseBV

parseSExpr :: T.Text -> Either String SExpr
parseSExpr = SC.decodeOne $ SC.asWellFormed $ SC.withLispComments (SC.mkParser parseAtom)
