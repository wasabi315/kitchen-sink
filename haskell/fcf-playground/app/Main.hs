{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.Type.Bool qualified as TB
import Data.Type.Equality
import Fcf
import Fcf.Data.List
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

type family NthImpl i xs where
  NthImpl 0 (x ':> _) = x
  NthImpl i (_ ':> xs) = NthImpl (i TN.- 1) (Eval xs)

data STake :: Nat -> Stream a -> Exp [a]

type instance Eval (STake n xs) = STakeImpl n xs

type family STakeImpl n xs where
  STakeImpl 0 _ = '[]
  STakeImpl n (x ':> xs) = x ': STakeImpl (n TN.- 1) (Eval xs)

-- Construction

data Iterate :: (s -> Exp a) -> (s -> Exp s) -> s -> Exp (Stream a)

type instance Eval (Iterate f g x) = (f @@ x) ':> Iterate f g (g @@ x)

-- Functor

type instance Eval (Map f (x ':> xs)) = (f @@ x) ':> (Map f =<< xs)

-- Examples

type Nats = Iterate Pure ((+) 1) 0

_testNats :: Eval (STake 10 =<< Nats) :~: '[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
_testNats = Refl

type Fibs = Iterate Fst FibF '(0, 1)

data FibF :: (Nat, Nat) -> Exp (Nat, Nat)

type instance Eval (FibF '(a, b)) = '(b, a TN.+ b)

_testFibs :: Eval (Nth 100 =<< Fibs) :~: 354224848179261915075
_testFibs = Refl

--------------------------------------------------------------------------------
-- Regular Language

infixl 1 \/

infixl 2 .

data Lang a = Lang Bool (a -> Exp (Lang a))

type family Accept l where
  Accept ('Lang a _) = a

type family Deriv l x where
  Deriv ('Lang _ d) x = d @@ x

type family Member xs l where
  Member '[] l = Accept l
  Member (x ': xs) l = Member xs (Deriv l x)

type Empty = 'Lang 'False EmptyD

data EmptyD :: a -> Exp (Lang a)

type instance Eval (EmptyD _) = Empty

type Epsilon = 'Lang 'True EpsilonD

data EpsilonD :: a -> Exp (Lang a)

type instance Eval (EpsilonD _) = Empty

type Single x = 'Lang 'False (SingleD x)

data SingleD :: a -> a -> Exp (Lang a)

type instance Eval (SingleD x y) = If (Eval (TyEq x y)) Epsilon Empty

type l1 \/ l2 = 'Lang (Accept l1 TB.|| Accept l2) (UnionD l1 l2)

data UnionD :: Lang a -> Lang a -> a -> Exp (Lang a)

type instance Eval (UnionD l1 l2 x) = Deriv l1 x \/ Deriv l2 x

type l1 . l2 = 'Lang (Accept l1 TB.&& Accept l2) (ConcatD l1 l2)

data ConcatD :: Lang a -> Lang a -> a -> Exp (Lang a)

type instance
  Eval (ConcatD l1 l2 x) =
    If
      (Accept l1)
      (Deriv l1 x . l2 \/ Deriv l2 x)
      (Deriv l1 x . l2)

type Kleene l = 'Lang 'True (KleeneD l)

data KleeneD :: Lang a -> a -> Exp (Lang a)

type instance Eval (KleeneD l x) = Deriv l x . Kleene l

-- Example

type OneOf xs = 'Lang 'False (OneOfD xs)

data OneOfD :: [a] -> a -> Exp (Lang a)

type instance Eval (OneOfD xs x) = If (Eval (Elem x xs)) Epsilon Empty

type Zero = Single '0'

type NonZero = OneOf '[ '1', '2', '3', '4', '5', '6', '7', '8', '9']

type Digit = Zero \/ NonZero

type Number = Zero \/ NonZero . Kleene Digit

_testNumber1 :: Member '[] Number :~: 'False
_testNumber1 = Refl

_testNumber2 :: Member '[ '0'] Number :~: 'True
_testNumber2 = Refl

_testNumber3 :: Member '[ '1'] Number :~: 'True
_testNumber3 = Refl

_testNumber4 :: Member '[ '0', '1'] Number :~: 'False
_testNumber4 = Refl

_testNumber5 :: Member '[ '1', '0', '0'] Number :~: 'True
_testNumber5 = Refl

--------------------------------------------------------------------------------
-- Fixpoint

data Fix :: (Exp a -> Exp a) -> Exp a

type instance Eval (Fix f) = Eval (f (Fix f))

_testFix :: Eval (Fix (ConstFn 1)) :~: 1
_testFix = Refl

--------------------------------------------------------------------------------

main = putStrLn "It typechecks!"
