{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Data.Coerce
import Data.Foldable
import Prelude hiding (curry)

main :: IO ()
main = for_ [ex1, ex2, ex3] \t -> do
  putStrLn "----------------"
  putStrLn $ prettyTerm [] 0 t ""
  let (t', i) = normalise t
  putStrLn $ prettyIso 0 i ""
  putStrLn $ prettyTerm [] 0 (nf0 t') ""

ex1 :: Term
ex1 = Pi "F" (Pi "_" (Pi "_" (Sigma "_" U U) U) U) $ Pi "G" (Pi "_" (Sigma "_" U U) U) $ Var 1 :@ Var 0

ex2 :: Term
ex2 = Pi "F" (Pi "_" (Sigma "_" U U) U) $ Pi "A" U $ Pi "B" U $ Var 2 :@ Pair (Var 1) (Var 0)

ex3 :: Term
ex3 =
  Pi "A" U $
    Pi "B" (Pi "_" (Var 0) U) $
      Pi "P" (Pi "_" (Sigma "x" (Var 1) (Var 1 :@ Var 0)) U) $
        Pi "p" (Sigma "x" (Var 2) (Var 2 :@ Var 0)) $
          Pi "q" (Sigma "y" (Var 3) (Var 3 :@ Var 0)) $
            Sigma "_" (Var 2 :@ Var 1) (Var 3 :@ Var 1)

--------------------------------------------------------------------------------

type Name = String

newtype Index = Index Int
  deriving newtype (Show, Ord, Eq, Num)

newtype MetaVar = MetaVar Int
  deriving newtype (Show, Ord, Eq, Num)

infixl 6 :@

data Term
  = Var Index
  | Meta MetaVar
  | U
  | Pi Name Term Term
  | Lam Name Term
  | Term :@ Term
  | Sigma Name Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  deriving (Show)

data Iso
  = -- | Γ |- A ~ A
    Refl
  | -- | Γ |- A ~ B => Γ |- B ~ A
    Sym Iso
  | -- | Γ |- A ~ B => Γ |- B ~ C => Γ |- A ~ C
    Trans Iso Iso
  | -- | Γ |- (x : (y : A) * B[y]) * C[x] ~ (x : A) * (y : B[x]) * C[(x, y)]
    Assoc
  | -- | Γ |- (x : A) * B ~ (x : B) * A
    Comm
  | -- | Γ |- (x : (y : A) * B[y]) -> C[x] ~ (x : A) (y : B[x]) -> C[(x, y)]
    Curry
  | PiCongL Iso
  | PiCongR Iso
  | SigmaCongL Iso
  | SigmaCongR Iso
  deriving (Show)

instance Semigroup Iso where
  Refl <> j = j
  i <> Refl = i
  i <> j = Trans i j

instance Monoid Iso where
  mempty = Refl

piCongL :: Iso -> Iso
piCongL = \case
  Refl -> Refl
  t -> PiCongL t

piCongR :: Iso -> Iso
piCongR = \case
  Refl -> Refl
  t -> PiCongR t

sigmaCongL :: Iso -> Iso
sigmaCongL = \case
  Refl -> Refl
  t -> SigmaCongL t

sigmaCongR :: Iso -> Iso
sigmaCongR = \case
  Refl -> Refl
  t -> SigmaCongR t

type Subst = Index -> Term

extendSubst :: Subst -> Subst
extendSubst _ 0 = Var 0
extendSubst s x = substitute (Var . (1 +)) (s (x - 1))

substitute :: (Index -> Term) -> Term -> Term
substitute subst = \case
  Var x -> subst x
  Meta m -> Meta m
  U -> U
  Pi x a b -> Pi x (substitute subst a) (substitute (extendSubst subst) b)
  Lam x t -> Lam x (substitute (extendSubst subst) t)
  t :@ u -> substitute subst t :@ substitute subst u
  Sigma x a b -> Sigma x (substitute subst a) (substitute (extendSubst subst) b)
  Pair t u -> Pair (substitute subst t) (substitute subst u)
  Fst t -> Fst (substitute subst t)
  Snd t -> Snd (substitute subst t)

--------------------------------------------------------------------------------

to :: Iso -> Term
to = \case
  Refl -> Lam "x" $ Var 0
  Sym i -> from i
  Trans i j -> Lam "x" $ to j :@ (to i :@ Var 0)
  Assoc -> Lam "p" $ Fst (Fst $ Var 0) `Pair` (Snd (Fst $ Var 0) `Pair` Snd (Var 0))
  Comm -> Lam "p" $ Snd (Var 0) `Pair` Fst (Var 0)
  Curry -> Lam "f" $ Lam "x" $ Lam "y" $ Var 2 :@ Pair (Var 1) (Var 0)
  PiCongL i -> Lam "f" $ Lam "x" $ Var 1 :@ (from i :@ Var 0)
  PiCongR i -> Lam "f" $ Lam "x" $ to i :@ (Var 1 :@ Var 0)
  SigmaCongL i -> Lam "p" $ (to i :@ Fst (Var 0)) `Pair` Snd (Var 0)
  SigmaCongR i -> Lam "p" $ Fst (Var 0) `Pair` (to i :@ Snd (Var 0))

from :: Iso -> Term
from = \case
  Refl -> Lam "x" $ Var 0
  Sym i -> to i
  Trans i j -> Lam "x" $ from i :@ (from j :@ Var 0)
  Assoc -> Lam "p" $ (Fst (Var 0) `Pair` Fst (Snd $ Var 0)) `Pair` Snd (Snd $ Var 0)
  Comm -> Lam "p" $ Snd (Var 0) `Pair` Fst (Var 0)
  Curry -> Lam "f" $ Lam "p" $ Var 1 :@ Fst (Var 0) :@ Snd (Var 0)
  PiCongL i -> Lam "f" $ Lam "x" $ Var 1 :@ (to i :@ Var 0)
  PiCongR i -> Lam "f" $ Lam "x" $ from i :@ (Var 1 :@ Var 0)
  SigmaCongL i -> Lam "p" $ (from i :@ Fst (Var 0)) `Pair` Snd (Var 0)
  SigmaCongR i -> Lam "p" $ Fst (Var 0) `Pair` (from i :@ Snd (Var 0))

normalise :: Term -> (Term, Iso)
normalise = \case
  Pi x a b ->
    let (a', ia) = normalise a
        b' = flip substitute b \case
          0 -> from ia :@ Var 0
          n -> Var n
        (b'', ib) = normalise b'
        (t, i) = curry (Pi x a' b'')
     in (t, piCongL ia <> piCongR ib <> i)
  Sigma x a b ->
    let (a', ia) = normalise a
        b' = flip substitute b \case
          0 -> from ia :@ Var 0
          n -> Var n
        (b'', ib) = normalise b'
        (t, i) = assoc (Sigma x a' b'')
     in (t, sigmaCongL ia <> sigmaCongR ib <> i)
  t -> (t, mempty)

curry :: Term -> (Term, Iso)
curry = \case
  Pi x (Sigma y a b) c ->
    let t = Pi y a $ Pi x b $ flip substitute c \case
          0 -> Var 1 `Pair` Var 0
          n -> Var (n + 1)
        (t', i) = curry t
     in (t', Curry <> i)
  Pi x a b ->
    let (b', i) = curry b
     in (Pi x a b', piCongR i)
  t -> (t, mempty)

assoc :: Term -> (Term, Iso)
assoc = \case
  Sigma x (Sigma y a b) c ->
    let t = Sigma y a $ Sigma x b $ flip substitute c \case
          0 -> Var 1 `Pair` Var 0
          n -> Var (n + 1)
        (t', i) = assoc t
     in (t', Assoc <> i)
  Sigma x a b ->
    let (b', i) = assoc b
     in (Sigma x a b', sigmaCongR i)
  t -> (t, mempty)

--------------------------------------------------------------------------------

newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show)

data Value
  = VRigid Level Spine
  | VFlex MetaVar Spine
  | VU
  | VPi Name Value (Value -> Value)
  | VLam Name (Value -> Value)
  | VSigma Name Value (Value -> Value)
  | VPair Value Value

data Spine
  = SNil
  | SApp Spine Value
  | SFst Spine
  | SSnd Spine

pattern VVar :: Level -> Value
pattern VVar x = VRigid x SNil

pattern VMeta :: MetaVar -> Value
pattern VMeta m = VFlex m SNil

eval :: [Value] -> Term -> Value
eval env = \case
  Var (Index x) -> env !! x
  Meta m -> VMeta m
  U -> VU
  Pi x a b -> VPi x (eval env a) \v -> eval (v : env) b
  Lam x t -> VLam x \v -> eval (v : env) t
  t :@ u -> vapp (eval env t) (eval env u)
  Sigma x a b -> VSigma x (eval env a) \v -> eval (v : env) b
  Pair t u -> VPair (eval env t) (eval env u)
  Fst t -> vfst (eval env t)
  Snd t -> vsnd (eval env t)

vapp :: Value -> Value -> Value
vapp = \cases
  (VLam _ f) u -> f u
  (VRigid x sp) u -> VRigid x (SApp sp u)
  _ _ -> error "vapp: not a function"

vfst :: Value -> Value
vfst = \case
  VPair t _ -> t
  VRigid x sp -> VRigid x (SFst sp)
  _ -> error "vfst: not a pair"

vsnd :: Value -> Value
vsnd = \case
  VPair _ t -> t
  VRigid x sp -> VRigid x (SSnd sp)
  _ -> error "vfst: not a pair"

quote :: Level -> Value -> Term
quote l = \case
  VRigid x sp -> quoteSpine l (Var $ coerce (l - x - 1)) sp
  VFlex m sp -> quoteSpine l (Meta m) sp
  VU -> U
  VPi x a b -> Pi x (quote l a) (quote (l + 1) (b $ VVar l))
  VLam x t -> Lam x (quote (l + 1) (t $ VVar l))
  VSigma x a b -> Sigma x (quote l a) (quote (l + 1) (b $ VVar l))
  VPair t u -> Pair (quote l t) (quote l u)

quoteSpine :: Level -> Term -> Spine -> Term
quoteSpine l hd = \case
  SNil -> hd
  SApp sp t -> quoteSpine l hd sp :@ quote l t
  SFst t -> Fst $ quoteSpine l hd t
  SSnd t -> Snd $ quoteSpine l hd t

nf0 :: Term -> Term
nf0 t = quote 0 (eval [] t)

--------------------------------------------------------------------------------

par :: Int -> Int -> ShowS -> ShowS
par p q = showParen (p > q)

projP, appP, sigmaP, piP, absP, pairP :: Int
projP = 5
appP = 4
sigmaP = 3
piP = 2
absP = 1
pairP = 0

freshen :: [Name] -> Name -> Name
freshen ns n
  | n `elem` ns = freshen ns (n ++ "\'")
  | otherwise = n

prettyTerm :: [Name] -> Int -> Term -> ShowS
prettyTerm = go
  where
    go ns p = \case
      Var (Index i) -> showString (ns !! i)
      Meta (MetaVar m) -> showChar '?' . shows m
      U -> showString "U"
      Pi "_" a b ->
        par p piP $ go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        par p piP $ piBind n ns a . goPi (n : ns) b
      Lam (freshen ns -> n) t ->
        par p absP $
          showString "λ " . showString n . goAbs (n : ns) t
      t :@ u -> par p appP $ go ns appP t . showChar ' ' . go ns projP u
      Sigma "_" a b ->
        par p sigmaP $ go ns appP a . showString " × " . go ("_" : ns) sigmaP b
      Sigma (freshen ns -> n) a b ->
        par p sigmaP $ piBind n ns a . showString " × " . go (n : ns) sigmaP b
      Fst t -> par p projP $ go ns projP t . showString ".1"
      Snd t -> par p projP $ go ns projP t . showString ".2"
      Pair t u -> par p pairP $ go ns absP t . showString " , " . go ns pairP u

    piBind n ns a =
      showString "("
        . showString n
        . showString " : "
        . go ns pairP a
        . showChar ')'

    goPi ns = \case
      Pi "_" a b -> showString " → " . go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        showChar ' ' . piBind n ns a . goPi (n : ns) b
      b -> showString " → " . go ns piP b

    goAbs ns = \case
      Lam (freshen ns -> n) t ->
        showChar ' ' . showString n . goAbs (n : ns) t
      t -> showString ". " . go ns absP t

prettyIso :: Int -> Iso -> ShowS
prettyIso p = \case
  Refl -> showString "refl"
  Sym (Sym i) -> prettyIso p i
  Sym i -> par p 11 $ prettyIso 12 i . showString "⁻¹"
  Trans Refl i -> prettyIso p i
  Trans i Refl -> prettyIso p i
  Trans i j -> par p 9 $ prettyIso 10 i . showString " · " . prettyIso 10 j
  Assoc -> showString "Assoc"
  Comm -> showString "Comm"
  Curry -> showString "Curry"
  PiCongL i -> par p 10 $ showString "ΠL " . prettyIso 11 i
  PiCongR i -> par p 10 $ showString "ΠR " . prettyIso 11 i
  SigmaCongL i -> par p 10 $ showString "ΣL " . prettyIso 11 i
  SigmaCongR i -> par p 10 $ showString "ΣR " . prettyIso 11 i
