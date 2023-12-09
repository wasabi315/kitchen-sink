{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import GHC.TypeNats

data Term i
  = Var i
  | App (Term i) (Term i)
  | Lam (Term (Maybe i))
  deriving (Show, Functor)

type ClosedTerm = forall i. Term i

class NatToIndex (n :: Nat) i where
  index :: i

instance {-# OVERLAPPING #-} NatToIndex 0 (Maybe x) where
  index = Nothing

instance {-# OVERLAPPABLE #-} (NatToIndex (n - 1) i) => NatToIndex n (Maybe i) where
  index = Just $ index @(n - 1)

var :: forall n i. (NatToIndex n i) => Term i
var = Var $ index @n

lam :: Term (Maybe i) -> Term i
lam = Lam

(@) :: Term i -> Term i -> Term i
(@) = App

infixl 1 @

_I :: ClosedTerm
_I = lam $ var @0

_K :: ClosedTerm
_K = lam $ lam $ var @1

_S :: ClosedTerm
_S = lam $ lam $ lam $ var @2 @ var @0 @ (var @1 @ var @0)

church :: Integer -> ClosedTerm
church = \n -> lam $ lam $ applyN n (var @1) (var @0)
  where
    applyN :: Integer -> Term i -> Term i -> Term i
    applyN 0 _ x = x
    applyN n f x = f @ applyN (n - 1) f x

pretty :: ClosedTerm -> String
pretty t = prettySub 0 t ""
  where
    prettySub :: Int -> Term Int -> ShowS
    prettySub _ (Var i) = shows i
    prettySub p (App x y) = showParen (p > 10) $ prettySub 10 x . prettySub 11 y
    prettySub p (Lam x) = showParen (p > 0) $ showChar 'λ' . prettySub 0 (maybe 0 succ <$> x)
