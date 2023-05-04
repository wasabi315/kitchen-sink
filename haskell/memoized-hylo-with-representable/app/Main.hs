{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

import Criterion.Main
import Data.Distributive
import Data.Distributive.Generic
import Data.Finite qualified as F
import Data.Functor.Rep
import Data.Vector.Sized qualified as V
import GHC.Generics (Generic1)
import GHC.TypeLits

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

merge :: Num a => BinTreeF a -> a
merge Tip = 1
merge (Branch x y) = x + y

split :: (Num a, Eq a) => a -> BinTreeF a
split 0 = Tip
split 1 = Tip
split n = Branch (n - 1) (n - 2)

fib :: Natural -> Natural
fib = hylo merge split

-- use Stream as the memo table
-- O(n) indexing so not quite efficient
fibMemo :: Natural -> Natural
fibMemo = hyloMemo @Stream merge split

-- statically-sized vector can be used as the memo table
-- if you know the upper bound of the input
-- O(1) indexing so very fast
fibMemoFin :: forall n. KnownNat n => F.Finite n -> Natural
fibMemoFin = hyloMemo @(V.Vector n) merge split

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
        ],
      bgroup "fibMemoFin" $
        [ bench "10" $ nf (fibMemoFin @11) 10,
          bench "20" $ nf (fibMemoFin @21) 20,
          bench "30" $ nf (fibMemoFin @31) 30,
          bench "35" $ nf (fibMemoFin @36) 35,
          bench "100" $ nf (fibMemoFin @101) 100,
          bench "1000" $ nf (fibMemoFin @1001) 1000,
          bench "10000" $ nf (fibMemoFin @10001) 10000,
          bench "50000" $ nf (fibMemoFin @50001) 50000
        ]
    ]
