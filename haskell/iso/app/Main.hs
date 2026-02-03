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
  let (t', i) = normalise0 t
  putStrLn $ prettyIso 0 i ""
  putStrLn $ prettyTerm [] 0 t' ""

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

infixl 6 :@, @

--------------------------------------------------------------------------------
-- Terms

type Name = String

newtype Index = Index Int
  deriving newtype (Show, Ord, Eq, Num)

data Term
  = Var Index
  | U
  | Pi Name Term Term
  | Lam Name Term
  | Term :@ Term
  | Sigma Name Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  deriving (Show)

--------------------------------------------------------------------------------
-- Values and NbE

newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show)

data Value
  = VRigid Level Spine
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

type Env = [Value]

eval :: Env -> Term -> Value
eval env = \case
  Var (Index x) -> env !! x
  U -> VU
  Pi x a b -> VPi x (eval env a) \v -> eval (v : env) b
  Lam x t -> VLam x \v -> eval (v : env) t
  t :@ u -> eval env t @ eval env u
  Sigma x a b -> VSigma x (eval env a) \v -> eval (v : env) b
  Pair t u -> VPair (eval env t) (eval env u)
  Fst t -> vfst (eval env t)
  Snd t -> vsnd (eval env t)

(@) :: Value -> Value -> Value
(@) = \cases
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
  _ -> error "vsnd: not a pair"

quote :: Level -> Value -> Term
quote l = \case
  VRigid x sp -> quoteSpine l (Var $ coerce (l - x - 1)) sp
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

--------------------------------------------------------------------------------
-- Isomorphisms

data Iso
  = --  -------
    --   A ~ A
    Refl
  | --   A ~ B
    --  -------
    --   B ~ A
    Sym Iso
  | --   A ~ B    B ~ C
    --  ----------------
    --       A ~ C
    Trans Iso Iso
  | --  ----------------------------------------------------------------
    --   (x : (y : A) * B[y]) * C[x] ~ (y : A) * (x : B[y]) * C[(x, y)]
    Assoc
  | --  ---------------
    --   A * B ~ B * A
    Comm
  | --  -------------------------------------------------------------------
    --   (x : (y : A) * B[y]) -> C[x] ~ (y : A) -> (x : B[y]) -> C[(x, y)]
    Curry
  | --                     i : A ~ A'
    --  ---------------------------------------------------
    --   (x : A) -> B[x] ~ (x : A') -> B[transportInv i x]
    PiCongL Iso
  | --             B[x] ~ B'[x]
    --  ------------------------------------
    --   (x : A) -> B[x] ~ (x : A) -> B'[x]
    PiCongR Iso
  | --                     i : A ~ A'
    --  -------------------------------------------------
    --   (x : A) * B[x] ~ (x : A') * B[transportInv i x]
    SigmaCongL Iso
  | --           B[x] ~ B'[x]
    --  ----------------------------------
    --   (x : A) * B[x] ~ (x : A) * B'[x]
    SigmaCongR Iso
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

-- transport along an isomorphism
transport :: Iso -> Value -> Value
transport = \cases
  Refl v -> v
  (Sym i) v -> transportInv i v
  (Trans i j) v -> transport j (transport i v)
  Assoc v -> vfst (vfst v) `VPair` (vsnd (vfst v) `VPair` vsnd v)
  Comm v -> vsnd v `VPair` vfst v
  Curry v -> VLam "x" \x -> VLam "y" \y -> v @ VPair x y
  (PiCongL i) v -> VLam "x" \x -> v @ transportInv i x
  (PiCongR i) v -> VLam "x" \x -> transport i (v @ x)
  (SigmaCongL i) v -> transport i (vfst v) `VPair` vsnd v
  (SigmaCongR i) v -> vfst v `VPair` transport i (vsnd v)

-- transport back
transportInv :: Iso -> Value -> Value
transportInv = \cases
  Refl v -> v
  (Sym i) v -> transport i v
  (Trans i j) v -> transportInv i (transportInv j v)
  Assoc v -> (vfst v `VPair` vfst (vsnd v)) `VPair` vsnd (vsnd v)
  Comm v -> vsnd v `VPair` vfst v
  Curry v -> VLam "p" \p -> v @ vfst p @ vsnd p
  (PiCongL i) v -> VLam "x" \x -> v @ (transport i x)
  (PiCongR i) v -> VLam "x" \x -> transportInv i (v @ x)
  (SigmaCongL i) v -> transportInv i (vfst v) `VPair` vsnd v
  (SigmaCongR i) v -> vfst v `VPair` transportInv i (vsnd v)

--------------------------------------------------------------------------------
-- Type normalisation

normalise0 :: Term -> (Term, Iso)
normalise0 t = normalise [] 0 (eval [] t)

-- compute the normalised type and isomorphism to it
normalise :: [Value] -> Level -> Value -> (Term, Iso)
normalise env l = \case
  VPi x a b ->
    let (a', ia) = normalise env l a
        (b', ib) = normalise (VVar l : env) (l + 1) (b $ transportInv ia $ VVar l)
        (t, i) = curry l $ eval env (Pi x a' b')
     in (t, piCongL ia <> piCongR ib <> i)
  VSigma x a b ->
    let (a', ia) = normalise env l a
        (b', ib) = normalise (VVar l : env) (l + 1) (b $ transportInv ia $ VVar l)
        (t, i) = assoc l $ eval env (Sigma x a' b')
     in (t, sigmaCongL ia <> sigmaCongR ib <> i)
  v -> (quote l v, mempty)

-- curryify top-level pi types
curry :: Level -> Value -> (Term, Iso)
curry l = \case
  VPi x (VSigma y a b) c ->
    let v = VPi y a \u -> VPi x (b u) \w -> c (VPair u w)
        (t, i) = curry l v
     in (t, Curry <> i)
  VPi x a b ->
    let a' = quote l a
        (b', i) = curry (l + 1) (b $ VVar l)
     in (Pi x a' b', piCongR i)
  v -> (quote l v, mempty)

-- make top-level sigma types right-nested
assoc :: Level -> Value -> (Term, Iso)
assoc l = \case
  VSigma x (VSigma y a b) c ->
    let v = VSigma y a \u -> VSigma x (b u) \w -> c (VPair u w)
        (t, i) = assoc l v
     in (t, Assoc <> i)
  VSigma x a b ->
    let a' = quote l a
        (b', i) = assoc (l + 1) (b $ VVar l)
     in (Sigma x a' b', sigmaCongR i)
  v -> (quote l v, mempty)

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
