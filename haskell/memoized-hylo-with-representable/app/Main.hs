{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

import Criterion.Main
import Data.Distributive
import Data.Distributive.Generic
import Data.Functor.Rep
import GHC.Generics (Generic1)
import Numeric.Natural

-- Infinite stream
data Stream a = a :< Stream a
  deriving (Functor, Generic1)

nats :: Stream Natural
nats = 0 :< fmap (+ 1) nats

(!) :: Stream a -> Natural -> a
(x :< _) ! 0 = x
(_ :< xs) ! n = xs ! (n - 1)

infixl 9 !

instance Distributive Stream where
  collect = genericCollect
  {-# INLINE collect #-}

instance Representable Stream where
  type Rep Stream = Natural
  index = (!)
  {-# INLINE index #-}
  tabulate = flip fmap nats
  {-# INLINE tabulate #-}

hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h where h = f . fmap h . g
{-# INLINE hylo #-}

-- Memoized hylo
hyloMemo ::
  forall t f b.
  (Representable t, Functor f) =>
  (f b -> b) ->
  (Rep t -> f (Rep t)) ->
  (Rep t -> b)
hyloMemo f g = index @t h where h = tabulate $ f . fmap (index h) . g
{-# INLINE hyloMemo #-}

data BinTreeF x
  = Tip
  | Branch !x !x
  deriving (Functor)

merge :: BinTreeF Natural -> Natural
merge Tip = 1
merge (Branch x y) = x + y

split :: Natural -> BinTreeF Natural
split 0 = Tip
split 1 = Tip
split n = Branch (n - 1) (n - 2)

fib :: Natural -> Natural
fib = hylo merge split

-- use Stream as a memo table
-- O(n) index so not quite efficient
fibMemo :: Natural -> Natural
fibMemo = hyloMemo @Stream merge split

main :: IO ()
main =
  defaultMain
    [ bgroup "fib" $
        [ bench "10" $ nf fib 10,
          bench "20" $ nf fib 20,
          bench "30" $ nf fib 30,
          bench "35" $ nf fib 35
        ],
      bgroup "fibMemo" $
        [ bench "10" $ nf fibMemo 10,
          bench "20" $ nf fibMemo 20,
          bench "30" $ nf fibMemo 30,
          bench "35" $ nf fibMemo 35,
          bench "100" $ nf fibMemo 100,
          bench "1000" $ nf fibMemo 1000,
          bench "10000" $ nf fibMemo 10000,
          bench "50000" $ nf fibMemo 50000
        ]
    ]
