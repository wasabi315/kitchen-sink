{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

import Data.Array qualified as A
import Data.Finite qualified as F
import Data.Functor.Rep
import Data.Monoid
import Data.Vector.Sized qualified as V

-- Table f ~ Rep f -> Rep f ~ Endo (Rep f)
newtype Table f = Table {getTable :: f (Rep f)}

table :: Representable f => (Rep f -> Rep f) -> Table f
table = Table . tabulate

instance Representable f => Semigroup (Table f) where
  Table f <> Table g = table (index f . index g)

instance Representable f => Monoid (Table f) where
  mempty = table id

-- Hand-crafted finite state machine for .*(.*007.*).*.

type N = 6

type State = F.Finite N

pattern S0, S1, S2, S3, S4, S5 :: State
pattern S0 <- (F.getFinite -> 0) where S0 = F.finite 0
pattern S1 <- (F.getFinite -> 1) where S1 = F.finite 1
pattern S2 <- (F.getFinite -> 2) where S2 = F.finite 2
pattern S3 <- (F.getFinite -> 3) where S3 = F.finite 3
pattern S4 <- (F.getFinite -> 4) where S4 = F.finite 4
pattern S5 <- (F.getFinite -> 5) where S5 = F.finite 5

{-# COMPLETE S0, S1, S2, S3, S4, S5 #-}

fsm :: State -> Char -> State
fsm S0 '(' = S1
fsm S0 _ = S0
fsm S1 '0' = S2
fsm S1 _ = S1
fsm S2 '0' = S3
fsm S2 _ = S1
fsm S3 '7' = S4
fsm S3 '0' = S3
fsm S3 _ = S1
fsm S4 ')' = S5
fsm S4 _ = S4
fsm S5 _ = S5

-- Regex can be considered as a [alphabet] -> Dual (Endo state)

letters :: A.Array Char (Table (V.Vector N))
letters = A.array (' ', 'z') [(i, table (`fsm` i)) | i <- [' ' .. 'z']]

matches :: String -> Bool
matches s = t `index` S0 == S5
  where
    t = getTable . getDual $ foldMap (Dual . (letters A.!)) s

main :: IO ()
main = do
  input <- getLine
  print $ matches input
