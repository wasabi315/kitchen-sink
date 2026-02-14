module Main where

import Control.Applicative
import Control.Monad
import Data.Coerce
import Data.Foldable
import Prelude hiding ((*))

infixr 5 -->

infixr 6 *

--------------------------------------------------------------------------------

main :: IO ()
main = for_ [ex1, ex2, ex3] \t -> do
  putStrLn $ prettyTerm [] 0 t "\n"
  let (t', i) = normalise0 t
  putStrLn $ "  ↓ " ++ prettyIso 0 i "\n"
  putStrLn $ prettyTerm [] 0 t' "\n"
  putStrLn "conversion function:"
  putStrLn $ "  " ++ prettyTerm [] 0 (quote 0 (VLam "x" $ transport i)) "\n\n"

ex1 :: Term
ex1 = Pi "F" (Pi "_" (Pi "_" (Sigma "_" U U) U) U) $ Pi "G" (Pi "_" (Sigma "_" U U) U) $ Var 1 :$$ Var 0

ex2 :: Term
ex2 = Pi "F" (Pi "_" (Sigma "_" U U) U) $ Pi "A" U $ Pi "B" U $ Var 2 :$$ Pair (Var 1) (Var 0)

ex3 :: Term
ex3 =
  Pi "A" U $
    Pi "B" (Pi "_" (Var 0) U) $
      Pi "P" (Pi "_" (Sigma "x" (Var 1) (Var 1 :$$ Var 0)) U) $
        Pi "p" (Sigma "x" (Var 2) (Var 2 :$$ Var 0)) $
          Pi "q" (Sigma "y" (Var 3) (Var 3 :$$ Var 0)) $
            Sigma "_" (Var 2 :$$ Var 1) (Var 3 :$$ Var 1)

exv :: Value
exv = VSigma "A" VU \_ -> VSigma "B" VU \_ -> VU

foldty1 :: Term
foldty1 = quote 0 $
  VPi "A" VU \a ->
    VPi "B" VU \b ->
      (a --> b --> b)
        --> b
        --> VTop "List" (SApp SNil a)
        --> b

foldty2 :: Term
foldty2 = quote 0 $
  VPi "A" VU \a ->
    VPi "B" VU \b ->
      (b * a --> b)
        --> VTop "List" (SApp SNil a)
        --> b
        --> b

--------------------------------------------------------------------------------
-- Terms

type Name = String

newtype Index = Index Int
  deriving newtype (Show, Ord, Eq, Num)

data Term
  = Var Index
  | Top Name
  | U
  | Pi Name Term Term
  | Lam Name Term
  | Term :$$ Term
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
  | VTop Name Spine
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

(-->) :: Value -> Value -> Value
a --> b = VPi "_" a \_ -> b

(*) :: Value -> Value -> Value
a * b = VSigma "_" a \_ -> b

type Env = [Value]

eval :: Env -> Term -> Value
eval env = \case
  Var (Index x) -> env !! x
  Top x -> VTop x SNil
  U -> VU
  Pi x a b -> VPi x (eval env a) \v -> eval (v : env) b
  Lam x t -> VLam x \v -> eval (v : env) t
  t :$$ u -> eval env t $$ eval env u
  Sigma x a b -> VSigma x (eval env a) \v -> eval (v : env) b
  Pair t u -> VPair (eval env t) (eval env u)
  Fst t -> vfst (eval env t)
  Snd t -> vsnd (eval env t)

($$) :: Value -> Value -> Value
($$) = \cases
  (VLam _ f) u -> f u
  (VRigid x sp) u -> VRigid x (SApp sp u)
  (VTop x sp) u -> VTop x (SApp sp u)
  _ _ -> error "($$): not a function"

vfst :: Value -> Value
vfst = \case
  VPair t _ -> t
  VRigid x sp -> VRigid x (SFst sp)
  VTop x sp -> VTop x (SFst sp)
  _ -> error "vfst: not a pair"

vsnd :: Value -> Value
vsnd = \case
  VPair _ t -> t
  VRigid x sp -> VRigid x (SSnd sp)
  VTop x sp -> VTop x (SSnd sp)
  _ -> error "vsnd: not a pair"

quote :: Level -> Value -> Term
quote l = \case
  VRigid x sp -> quoteSpine l (Var $ coerce (l - x - 1)) sp
  VTop x sp -> quoteSpine l (Top x) sp
  VU -> U
  VPi x a b -> Pi x (quote l a) (quote (l + 1) (b $ VVar l))
  VLam x t -> Lam x (quote (l + 1) (t $ VVar l))
  VSigma x a b -> Sigma x (quote l a) (quote (l + 1) (b $ VVar l))
  VPair t u -> Pair (quote l t) (quote l u)

quoteSpine :: Level -> Term -> Spine -> Term
quoteSpine l hd = \case
  SNil -> hd
  SApp sp t -> quoteSpine l hd sp :$$ quote l t
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
  | -- ---------------------------------------------
    --  (x : A) (y : B) -> C ~ (y : B) (x : A) -> C
    Swap
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

sym :: Iso -> Iso
sym = \case
  Refl -> Refl
  Sym i -> i
  i -> Sym i

piCongL :: Iso -> Iso
piCongL = \case
  Refl -> Refl
  i -> PiCongL i

piCongR :: Iso -> Iso
piCongR = \case
  Refl -> Refl
  i -> PiCongR i

sigmaCongL :: Iso -> Iso
sigmaCongL = \case
  Refl -> Refl
  i -> SigmaCongL i

sigmaCongR :: Iso -> Iso
sigmaCongR = \case
  Refl -> Refl
  i -> SigmaCongR i

-- transport along an isomorphism
transport :: Iso -> Value -> Value
transport = \cases
  Refl v -> v
  (Sym i) v -> transportInv i v
  (Trans i j) v -> transport j (transport i v)
  Assoc v -> vfst (vfst v) `VPair` (vsnd (vfst v) `VPair` vsnd v)
  Comm v -> vsnd v `VPair` vfst v
  Curry v -> VLam "x" \x -> VLam "y" \y -> v $$ VPair x y
  Swap v -> VLam "y" \y -> VLam "x" \x -> v $$ x $$ y
  (PiCongL i) v -> VLam "x" \x -> v $$ transportInv i x
  (PiCongR i) v -> VLam "x" \x -> transport i (v $$ x)
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
  Curry v -> VLam "p" \p -> v $$ vfst p $$ vsnd p
  Swap v -> VLam "x" \x -> VLam "y" \y -> v $$ y $$ x
  (PiCongL i) v -> VLam "x" \x -> v $$ transport i x
  (PiCongR i) v -> VLam "x" \x -> transportInv i (v $$ x)
  (SigmaCongL i) v -> transportInv i (vfst v) `VPair` vsnd v
  (SigmaCongR i) v -> vfst v `VPair` transportInv i (vsnd v)

--------------------------------------------------------------------------------
-- Type normalisation

normalise0 :: Term -> (Term, Iso)
normalise0 t = normalise 0 (eval [] t)

-- compute the normalised type and isomorphism to it
normalise :: Level -> Value -> (Term, Iso)
normalise l = \case
  VPi x a b -> normalisePi l x a b
  VSigma x a b -> normaliseSigma l x a b
  v -> (quote l v, mempty)

-- currying
normalisePi :: Level -> Name -> Value -> (Value -> Value) -> (Term, Iso)
normalisePi l x = \cases
  (VSigma y a b) c ->
    let (t, i) = normalisePi l y a \u -> VPi x (b u) \v -> c (VPair u v)
     in (t, Curry <> i)
  a b ->
    let (ta, ia) = normalise l a
        (tb, ib) = normalise (l + 1) (b (transportInv ia (VVar l)))
     in (Pi x ta tb, piCongL ia <> piCongR ib)

-- make sigmas more right-nested
normaliseSigma :: Level -> Name -> Value -> (Value -> Value) -> (Term, Iso)
normaliseSigma l x = \cases
  (VSigma y a b) c ->
    let (t, i) = normaliseSigma l y a \u -> VSigma x (b u) \v -> c (VPair u v)
     in (t, Assoc <> i)
  a b ->
    let (ta, ia) = normalise l a
        (tb, ib) = normalise (l + 1) (b (transportInv ia (VVar l)))
     in (Sigma x ta tb, sigmaCongL ia <> sigmaCongR ib)

--------------------------------------------------------------------------------
-- Conversion modulo isomorphism

convIso0 :: (MonadPlus m) => Term -> Term -> m Iso
convIso0 t u = fmap (\(i, j) -> i <> sym j) $ convIso 0 (eval [] t) (eval [] u)

convIso :: (MonadPlus m) => Level -> Value -> Value -> m (Iso, Iso)
convIso l = \cases
  -- pi is only convertible with pi under the isomorphisms we consider here
  (VPi _ a b) (VPi _ a' b') -> convPi l a b a' b'
  (VPi {}) _ -> empty
  _ (VPi {}) -> empty
  -- likewise
  (VSigma _ a b) (VSigma _ a' b') -> convSigma l a b a' b'
  (VSigma {}) _ -> empty
  _ (VSigma {}) -> empty
  t u -> (Refl, Refl) <$ guard (conv l t u)

depend :: Level -> Level -> Value -> Bool
depend from to = go to
  where
    go l = \case
      VRigid x sp -> (from <= x && x <= to) || goSpine l sp
      VTop _ sp -> goSpine l sp
      VU -> False
      VPi _ a b -> go l a || goBinder l b
      VLam _ t -> goBinder l t
      VSigma _ a b -> go l a || goBinder l b
      VPair t u -> go l t || go l u

    goBinder l t = go (l + 1) (t $ VVar l)

    goSpine l = \case
      SNil -> False
      SApp sp t -> goSpine l sp || go l t
      SFst sp -> goSpine l sp
      SSnd sp -> goSpine l sp

pickDomain ::
  forall m.
  (MonadPlus m) =>
  Level ->
  Value ->
  (Value -> Value) ->
  m (Value, Value -> Value, Iso)
pickDomain topL a b = pure (a, b, Refl) <|> go topL b
  where
    -- matching under binders :(
    go :: Level -> (Value -> Value) -> m (Value, Value -> Value, Iso)
    go l c = case c (VVar l) of
      VPi _ c1 c2 ->
        asum
          [ do
              guard $ not (depend topL l c1)
              pure
                ( c1,
                  (\vc1 -> deletePi (l - topL + 1) vc1 (VPi "x" a b)),
                  swaps (l - topL)
                ),
            go (l + 1) c2
          ]
      _ -> empty

    deletePi :: Level -> Value -> Value -> Value
    deletePi = \cases
      0 vc1 (VPi _ _ c2) -> c2 vc1
      i vc1 (VPi y d e) -> VPi y d (deletePi (i - 1) vc1 . e)
      _ _ _ -> error "not a pi"

    swaps :: Level -> Iso
    swaps = \case
      0 -> Swap
      i -> piCongR (swaps (i - 1)) <> Swap

convPi :: (MonadPlus m) => Level -> Value -> (Value -> Value) -> Value -> (Value -> Value) -> m (Iso, Iso)
convPi l = \cases
  -- Curry first
  (VSigma x a b) c (VSigma x' a' b') c' -> do
    (i, i') <-
      convPi
        l
        a
        (\u -> VPi x (b u) \v -> c (VPair u v))
        a'
        (\u' -> VPi x' (b' u') \v' -> c' (VPair u' v'))
    pure (Curry <> i, Curry <> i')
  (VSigma x a b) c a' b' -> do
    (i, i') <-
      convPi
        l
        a
        (\u -> VPi x (b u) \v -> c (VPair u v))
        a'
        b'
    pure (Curry <> i, i')
  a b (VSigma x' a' b') c' -> do
    (i, i') <-
      convPi
        l
        a
        b
        a'
        (\u' -> VPi x' (b' u') \v' -> c' (VPair u' v'))
    pure (i, Curry <> i')
  -- Then permute domain
  a b a' b' -> do
    (a'', b'', i) <- pickDomain l a' b'
    (ia, ia') <- convIso l a a''
    (ib, ib') <- convIso (l + 1) (b (transportInv ia (VVar l))) (b'' (transportInv ia' (VVar l)))
    pure (piCongL ia <> piCongR ib, i <> piCongL ia' <> piCongR ib')

pickProjection ::
  forall m.
  (MonadPlus m) =>
  Level ->
  Value ->
  (Value -> Value) ->
  m (Value, Value -> Value, Iso)
pickProjection topL a b = pure (a, b, Refl) <|> go topL b
  where
    -- matching under binders :(
    go :: Level -> (Value -> Value) -> m (Value, Value -> Value, Iso)
    go l c = case c (VVar l) of
      VSigma _ c1 c2 ->
        asum
          [ do
              guard $ not (depend topL l c1)
              pure
                ( c1,
                  (\vc1 -> deleteSigma (l - topL + 1) vc1 (VSigma "x" a b)),
                  comms (l - topL)
                ),
            go (l + 1) c2
          ]
      c' -> do
        guard $ not (depend topL l c')
        pure
          ( c',
            (\vc' -> deleteSigma (l - topL + 1) vc' (VSigma "a" a b)),
            comms (l - topL)
          )

    deleteSigma :: Level -> Value -> Value -> Value
    deleteSigma = \cases
      0 vc1 (VSigma _ _ c2) -> c2 vc1
      1 vc1 (VSigma y d e) -> case e (VVar (-1)) of
        VSigma {} -> VSigma y d (deleteSigma 0 vc1 . e)
        _ -> d
      i vc1 (VSigma y d e) -> VSigma y d (deleteSigma (i - 1) vc1 . e)
      _ _ _ -> error "not a sigma"

    comms :: Level -> Iso
    comms = \case
      0 -> Comm
      i -> sigmaCongR (comms (i - 1)) <> Comm

convSigma :: (MonadPlus m) => Level -> Value -> (Value -> Value) -> Value -> (Value -> Value) -> m (Iso, Iso)
convSigma l = \cases
  -- Assoc first
  (VSigma x a b) c (VSigma x' a' b') c' -> do
    (i, i') <-
      convSigma
        l
        a
        (\u -> VSigma x (b u) \v -> c (VPair u v))
        a'
        (\u' -> VSigma x' (b' u') \v' -> c' (VPair u' v'))
    pure (Assoc <> i, Assoc <> i')
  (VSigma x a b) c a' b' -> do
    (i, i') <-
      convSigma
        l
        a
        (\u -> VSigma x (b u) \v -> c (VPair u v))
        a'
        b'
    pure (Assoc <> i, i')
  a b (VSigma x' a' b') c' -> do
    (i, i') <-
      convSigma
        l
        a
        b
        a'
        (\u' -> VSigma x' (b' u') \v' -> c' (VPair u' v'))
    pure (i, Assoc <> i')
  -- Then permute projections
  a b a' b' -> do
    (a'', b'', i) <- pickProjection l a' b'
    (ia, ia') <- convIso l a a''
    (ib, ib') <- convIso (l + 1) (b (transportInv ia (VVar l))) (b'' (transportInv ia' (VVar l)))
    pure (sigmaCongL ia <> sigmaCongR ib, i <> sigmaCongL ia' <> sigmaCongR ib')

conv :: Level -> Value -> Value -> Bool
conv l = \cases
  (VRigid x sp) (VRigid x' sp') ->
    x == x' && convSpine l sp sp'
  (VTop x sp) (VTop x' sp') ->
    x == x' && convSpine l sp sp'
  VU VU -> True
  (VPi _ a b) (VPi _ a' b') ->
    conv l a a' && conv (l + 1) (b $ VVar l) (b' $ VVar l)
  (VLam _ t) (VLam _ t') ->
    conv (l + 1) (t $ VVar l) (t' $ VVar l)
  (VLam _ t) u ->
    conv (l + 1) (t $ VVar l) (u $$ VVar l)
  t (VLam _ u) ->
    conv (l + 1) (t $$ VVar l) (u $ VVar l)
  (VSigma _ a b) (VSigma _ a' b') ->
    conv l a a' && conv (l + 1) (b $ VVar l) (b' $ VVar l)
  (VPair t u) (VPair t' u') ->
    conv l t t' && conv l u u'
  (VPair t u) v ->
    conv l t (vfst v) && conv l u (vsnd v)
  t (VPair u v) ->
    conv l (vfst t) u && conv l (vsnd t) v
  _ _ -> False

convSpine :: Level -> Spine -> Spine -> Bool
convSpine l = \cases
  SNil SNil -> True
  (SApp sp t) (SApp sp' t') -> convSpine l sp sp' && conv l t t'
  (SFst sp) (SFst sp') -> convSpine l sp sp'
  (SSnd sp) (SSnd sp') -> convSpine l sp sp'
  _ _ -> False

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
  | n `elem` ns = go 0
  | otherwise = n
  where
    go (i :: Int)
      | n' `notElem` ns = n'
      | otherwise = go (i + 1)
      where
        n' = n ++ map sub (show i)

    sub = \case
      '0' -> '₀'
      '1' -> '₁'
      '2' -> '₂'
      '3' -> '₃'
      '4' -> '₄'
      '5' -> '₅'
      '6' -> '₆'
      '7' -> '₇'
      '8' -> '₈'
      '9' -> '₉'
      _ -> error "impossible"

prettyTerm :: [Name] -> Int -> Term -> ShowS
prettyTerm = go
  where
    go ns p = \case
      Var (Index i) -> showString (ns !! i)
      Top x -> showString x
      U -> showString "U"
      Pi "_" a b ->
        par p piP $ go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        par p piP $ piBind n ns a . goPi (n : ns) b
      Lam (freshen ns -> n) t ->
        par p absP $
          showString "λ " . showString n . goAbs (n : ns) t
      t :$$ u -> par p appP $ go ns appP t . showChar ' ' . go ns projP u
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
  Sym i -> par p 11 $ prettyIso 12 i . showString " ⁻¹"
  Trans i j -> par p 9 $ prettyIso 10 i . showString " · " . prettyIso 10 j
  Assoc -> showString "Assoc"
  Comm -> showString "Comm"
  Curry -> showString "Curry"
  Swap -> showString "Swap"
  PiCongL i -> par p 10 $ showString "ΠL " . prettyIso 11 i
  PiCongR i -> par p 10 $ showString "ΠR " . prettyIso 11 i
  SigmaCongL i -> par p 10 $ showString "ΣL " . prettyIso 11 i
  SigmaCongR i -> par p 10 $ showString "ΣR " . prettyIso 11 i
