{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Type.Equality
import Fcf
import Fcf.Data.Nat
import GHC.TypeNats qualified as TN

--------------------------------------------------------------------------------
-- Type-level Infinite Streams

-- Exp can be seen as a thunk that can be forced by Eval.
data Stream a = a :> Exp (Stream a)

-- Elimination

data SHead :: Stream a -> Exp a

type instance Eval (SHead (x ':> _)) = x

data STail :: Stream a -> Exp (Stream a)

type instance Eval (STail (_ ':> xs)) = Eval xs

data Nth :: Nat -> Stream a -> Exp a

type instance Eval (Nth n xs) = NthImpl n xs

type family NthImpl (i :: Nat) (xs :: Stream a) :: a where
  NthImpl 0 (x ':> _) = x
  NthImpl i (_ ':> xs) = NthImpl (i TN.- 1) (Eval xs)

data Take :: Nat -> Stream a -> Exp [a]

type instance Eval (Take n xs) = TakeImpl n xs

type family TakeImpl (n :: Nat) (xs :: Stream a) :: [a] where
  TakeImpl 0 _ = '[]
  TakeImpl n (x ':> xs) = x ': TakeImpl (n TN.- 1) (Eval xs)

-- Construction

data Repeat :: a -> Exp (Stream a)

type instance Eval (Repeat x) = x ':> Repeat x

data Iterate' :: (a -> Exp a) -> a -> Exp (Stream a)

-- (f x) is forced thus the name
type instance Eval (Iterate' f x) = x ':> Iterate' f (f @@ x)

data Unfold :: (b -> Exp (a, b)) -> b -> Exp (Stream a)

data UnfoldCase :: (b -> Exp (a, b)) -> (a, b) -> Exp (Stream a)

type instance Eval (Unfold f b) = Eval (UnfoldCase f (f @@ b))

type instance Eval (UnfoldCase f '(a, b)) = a ':> Unfold f b

-- Functor

type instance Eval (Map f (x ':> xs)) = (f @@ x) ':> (Map f =<< xs)

-- Examples

data Nats :: Exp (Stream Nat)

type instance Eval Nats = Eval (Iterate' ((+) 1) 0)

testNats :: Eval (Take 10 =<< Nats) :~: '[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
testNats = Refl

data Fibs :: Exp (Stream Nat)

type instance Eval Fibs = Eval (Unfold FibF '(0, 1))

data FibF :: (Nat, Nat) -> Exp (Nat, (Nat, Nat))

type instance Eval (FibF '(a, b)) = '(a, '(b, a TN.+ b))

testFibs :: Eval (Nth 100 =<< Fibs) :~: 354224848179261915075
testFibs = Refl

--------------------------------------------------------------------------------
-- Fixpoint

data Fix :: (Exp a -> Exp a) -> Exp a

type instance Eval (Fix f) = Eval (f (Fix f))

testFix :: Eval (Fix (ConstFn 1)) :~: 1
testFix = Refl

--------------------------------------------------------------------------------

main = putStrLn "It typechecks!"
