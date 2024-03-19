{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}

-- Ref: https://okmij.org/ftp/tagless-final/ski.pdf

main :: IO ()
main = do
  print $ church @PLam 5
  print $ convert @PSKI (church 5)

--------------------------------------------------------------------------------
-- Tagless-final encoding of the simply-typed lambda calculus and the SKI combinator calculus

infixl 1 $$

class Applicable repr where
  ($$) :: repr (a -> b) -> repr a -> repr b

class (forall g. Applicable (repr g)) => Lam repr where
  -- de Bruijn indices
  zero :: repr (a, g) a
  suc :: repr (b, g) a -> repr (c, (b, g)) a

  -- abstraction
  lam :: repr (a, g) b -> repr g (a -> b)

class (Applicable repr) => SKI repr where
  _I :: repr (a -> a)
  _K :: repr (a -> b -> a)
  _S :: repr ((a -> b -> c) -> (a -> b) -> a -> c)
  _B :: repr ((b -> c) -> (a -> b) -> a -> c)
  _C :: repr ((a -> b -> c) -> b -> a -> c)

instance (Lam repr) => SKI (repr g) where
  _I = lam zero
  _K = lam $ lam (suc zero)
  _S = lam $ lam $ lam $ suc (suc zero) $$ zero $$ (suc zero $$ zero)
  _B = lam $ lam $ lam $ suc (suc zero) $$ (suc zero $$ zero)
  _C = lam $ lam $ lam $ suc (suc zero) $$ zero $$ suc zero

church :: (Lam repr) => Int -> repr g ((a -> a) -> a -> a)
church 0 = lam $ lam zero
church n = lam $ lam $ suc zero $$ (church (n - 1) $$ suc zero $$ zero)

--------------------------------------------------------------------------------
-- Bracket abstraction

data Conv repr g a where
  Done :: repr a -> Conv repr g a
  Top :: Conv repr (a, g) a
  UseTop :: Conv repr g (a -> b) -> Conv repr (a, g) b
  IgnoreTop :: Conv repr g b -> Conv repr (a, g) b

convert :: Conv repr () a -> repr a
convert (Done t) = t

instance (SKI repr) => Applicable (Conv repr g) where
  Done t $$ Done u = Done (t $$ u)
  Done t $$ Top = UseTop (Done t)
  Done t $$ UseTop u = UseTop (Done (_B $$ t) $$ u)
  Done t $$ IgnoreTop u = IgnoreTop (Done t $$ u)
  Top $$ Done t = UseTop (Done (_C $$ _I $$ t))
  Top $$ UseTop u = UseTop (Done (_S $$ _I) $$ u)
  Top $$ IgnoreTop u = UseTop (Done (_C $$ _I) $$ u)
  UseTop t $$ Done u = UseTop (Done (_C $$ _C $$ u) $$ t)
  UseTop t $$ Top = UseTop (Done _S $$ t $$ Done _I)
  UseTop t $$ UseTop u = UseTop (Done _S $$ t $$ u)
  UseTop t $$ IgnoreTop u = UseTop (Done _C $$ t $$ u)
  IgnoreTop t $$ Done u = IgnoreTop (t $$ Done u)
  IgnoreTop t $$ Top = UseTop t
  IgnoreTop t $$ UseTop u = UseTop (Done _B $$ t $$ u)
  IgnoreTop t $$ IgnoreTop u = IgnoreTop (t $$ u)

instance (SKI repr) => Lam (Conv repr) where
  zero = Top
  suc = IgnoreTop
  lam (Done t) = Done (_K $$ t)
  lam Top = Done _I
  lam (UseTop t) = t
  lam (IgnoreTop t) = Done _K $$ t

--------------------------------------------------------------------------------
-- Pretty printing

newtype Ix = Ix Int deriving (Show, Num, Enum) via Int

newtype PLam g a = PLam (Ix -> Int -> ShowS)

instance Show (PLam g a) where
  showsPrec prec (PLam f) = f 0 prec

instance Applicable (PLam g) where
  PLam f $$ PLam x = PLam \_ prec -> showParen (prec > 10) (f 0 10 . x 0 11)

instance Lam PLam where
  zero = PLam \ix _ -> shows ix
  suc (PLam f) = PLam \ix prec -> f (succ ix) prec
  lam (PLam f) = PLam \_ prec -> showParen (prec > 0) $ showChar 'λ' . f 0 0

newtype PSKI a = PSKI (Int -> ShowS)

instance Show (PSKI a) where
  showsPrec prec (PSKI f) = f prec

instance Applicable PSKI where
  PSKI f $$ PSKI x = PSKI \prec -> showParen (prec > 10) (f 10 . x 11)

instance SKI PSKI where
  _I = PSKI \_ -> showString "I"
  _K = PSKI \_ -> showString "K"
  _S = PSKI \_ -> showString "S"
  _B = PSKI \_ -> showString "B"
  _C = PSKI \_ -> showString "C"
