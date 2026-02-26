{-# LANGUAGE MultiWayIf #-}

module Main where

import Control.Applicative
import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Parallel.Strategies
import Data.ByteString qualified as BS
import Data.Coerce
import Data.Foldable
import Data.Maybe
import Data.Monoid
import Data.String
import Flat
import System.Environment
import Prelude hiding (curry)

infixr 5 -->

infixr 6 ***

--------------------------------------------------------------------------------

main :: IO ()
main =
  getArgs >>= \case
    ["gen"] -> do
      let ts = everyNth 5000 $ map fst $ normalisePermute0 compSquareH
      BS.writeFile "bench.bin" (flat ts)
    ["bench"] -> do
      Right ts <- unflat @[Term] <$> BS.readFile "bench.bin"
      ts <- evaluate $ force ts
      for_ ts \t -> fromJust (convIso0 compSquareH t) `seq` pure ()
    _ -> error "invalid argument"

everyNth :: Int -> [a] -> [a]
everyNth n xs
  | n <= 0 = []
  | otherwise = case drop (n - 1) xs of
      y : ys -> y : everyNth n ys
      [] -> []

compSquareH :: Term
compSquareH = quote 0 $
  VPi "A" VU \a ->
    VPi "a00" a \a00 -> VPi "a01" a \a01 -> VPi "a02" a \a02 ->
      VPi "a10" a \a10 -> VPi "a11" a \a11 -> VPi "a12" a \a12 ->
        VPi "a0_" ("Eq" $$ a $$ a00 $$ a01) \a0_ ->
          VPi "b0_" ("Eq" $$ a $$ a01 $$ a02) \b0_ ->
            VPi "a1_" ("Eq" $$ a $$ a10 $$ a11) \a1_ ->
              VPi "b1_" ("Eq" $$ a $$ a11 $$ a12) \b1_ ->
                VPi "a_0" ("Eq" $$ a $$ a00 $$ a10) \a_0 ->
                  VPi "a_1" ("Eq" $$ a $$ a01 $$ a11) \a_1 ->
                    VPi "a_2" ("Eq" $$ a $$ a02 $$ a12) \a_2 ->
                      ("Square" $$ a $$ a0_ $$ a1_ $$ a_0 $$ a_1)
                        --> ("Square" $$ a $$ b0_ $$ b1_ $$ a_1 $$ a_2)
                        --> ( "Square"
                                $$ a
                                $$ ("compPath" $$ a $$ a00 $$ a01 $$ a02 $$ a0_ $$ b0_)
                                $$ ("compPath" $$ a $$ a10 $$ a11 $$ a12 $$ a1_ $$ b1_)
                                $$ a_0
                                $$ a_2
                            )

ex1 :: Term
ex1 = quote 0 $
  VPi "F" ((VU *** VU --> VU) --> VU) \f ->
    VPi "G" (VU *** VU --> VU) \g ->
      f $$ g

ex2 :: Term
ex2 = quote 0 $
  VPi "F" (VU *** VU --> VU) \f ->
    VPi "A" VU \a ->
      VPi "B" VU \b ->
        f $$ VPair a b

ex3 :: Term
ex3 = quote 0 $
  VPi "A" VU \a ->
    VPi "B" (a --> VU) \b ->
      VPi "P" (VSigma "x" a (\x -> b $$ x) --> VU) \p ->
        VPi "p" (VSigma "x" a (\x -> b $$ x)) \p' ->
          VPi "q" (VSigma "y" a (\y -> b $$ y)) \q ->
            (p $$ p') *** (p $$ q)

foldty1 :: Term
foldty1 = quote 0 $
  VPi "A" VU \a ->
    VPi "B" VU \b ->
      (a --> b --> b)
        --> b
        --> ("List" $$ a)
        --> b

foldty2 :: Term
foldty2 = quote 0 $
  VPi "A" VU \a ->
    VPi "B" VU \b ->
      (b *** a --> b)
        --> ("List" $$ a)
        --> b
        --> b

foldty3 :: Term
foldty3 = quote 0 $
  VPi "A" VU \a ->
    VPi "B" VU \b ->
      ("List" $$ a)
        --> ((b *** a --> b) *** b)
        --> b

listind1 :: Term
listind1 = quote 0 $
  VPi "A" VU \a ->
    VPi "P" (("List" $$ a) --> VU) \p ->
      ( VPi "x" a \x ->
          VPi "xs" ("List" $$ a) \xs ->
            (p $$ xs)
              --> (p $$ ("cons" $$ a $$ x $$ xs))
      )
        --> (p $$ ("nil" $$ a))
        --> VPi "xs" ("List" $$ a) \xs -> p $$ xs

listind2 :: Term
listind2 = quote 0 $
  VPi "A" VU \a ->
    VPi "P" (("List" $$ a) --> VU) \p ->
      ( VPi "t" (VSigma "xs" ("List" $$ a) \xs -> p $$ xs) \t ->
          VPi "x" a \x ->
            (p $$ ("cons" $$ a $$ x $$ vfst t))
      )
        --> VPi "xs" ("List" $$ a) \xs ->
          (p $$ ("nil" $$ a))
            --> (p $$ xs)

square1, square2 :: Term
square1 = quote 0 $
  VPi "A" VU \a ->
    VPi "a00" a \a00 -> VPi "a01" a \a01 ->
      VPi "a10" a \a10 -> VPi "a11" a \a11 ->
        ("Eq" $$ a $$ a00 $$ a01)
          --> ("Eq" $$ a $$ a10 $$ a11)
          --> ("Eq" $$ a $$ a00 $$ a10)
          --> ("Eq" $$ a $$ a01 $$ a11)
          --> VU
square2 = quote 0 $
  VPi "A" VU \a ->
    VPi "a11" a \a11 ->
      VPi "a10" a \a10 ->
        ("Eq" $$ a $$ a10 $$ a11)
          --> VPi "a01" a \a01 ->
            ("Eq" $$ a $$ a01 $$ a11)
              --> VPi "a00" a \a00 ->
                ("Eq" $$ a $$ a00 $$ a10)
                  --> ("Eq" $$ a $$ a00 $$ a01)
                  --> VU

--------------------------------------------------------------------------------
-- Util

infix 2 //

-- strict pair construction
(//) :: a -> b -> (a, b)
a // b = (a, b)

foldMapA :: (Alternative f, Foldable t) => (a -> f b) -> t a -> f b
foldMapA f = getAlt . foldMap (Alt . f)

parFoldMapA :: (Alternative m) => Int -> Strategy (m b) -> (a -> m b) -> [a] -> m b
parFoldMapA fuel strat f xs =
  if fuel > 0
    then asum $ parMap strat f xs
    else foldMapA f xs

--------------------------------------------------------------------------------
-- Terms

type Name = String

newtype Index = Index Int
  deriving stock (Generic)
  deriving newtype (Show, Ord, Eq, Num)
  deriving anyclass (NFData, Flat)

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
  deriving stock (Show, Generic)
  deriving anyclass (NFData, Flat)

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
a --> b = VPi "_" a \ ~_ -> b

(***) :: Value -> Value -> Value
a *** b = VSigma "_" a \ ~_ -> b

instance IsString Value where
  fromString s = VTop s SNil

type Env = [Value]

eval :: Env -> Term -> Value
eval env = \case
  Var (Index x) -> env !! x
  Top x -> VTop x SNil
  U -> VU
  Pi x a b -> VPi x (eval env a) \ ~v -> eval (v : env) b
  Lam x t -> VLam x \v -> eval (v : env) t
  t :$$ u -> eval env t $$ eval env u
  Sigma x a b -> VSigma x (eval env a) \ ~v -> eval (v : env) b
  Pair t u -> VPair (eval env t) (eval env u)
  Fst t -> vfst (eval env t)
  Snd t -> vsnd (eval env t)

($$) :: Value -> Value -> Value
t $$ u = case t of
  VLam _ f -> f u
  VRigid x sp -> VRigid x (SApp sp u)
  VTop x sp -> VTop x (SApp sp u)
  _ -> error "($$): not a lambda"

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
  | -- ---------------------------------------------
    --  (x : A) * (y : B) * C ~ (y : B) * (x : A) * C
    --
    -- derivable from comm and assoc
    SigmaSwap
  | --  -------------------------------------------------------------------
    --   (x : (y : A) * B[y]) -> C[x] ~ (y : A) -> (x : B[y]) -> C[(x, y)]
    Curry
  | -- ---------------------------------------------
    --  (x : A) (y : B) -> C ~ (y : B) (x : A) -> C
    --
    -- derivable from comm and curry
    PiSwap
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
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

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
transport i v = case i of
  Refl -> v
  Sym i -> transportInv i v
  Trans i j -> transport j (transport i v)
  Assoc -> vfst (vfst v) `VPair` (vsnd (vfst v) `VPair` vsnd v)
  Comm -> vsnd v `VPair` vfst v
  SigmaSwap -> vfst (vsnd v) `VPair` (vfst v `VPair` vsnd (vsnd v))
  Curry -> VLam "x" \x -> VLam "y" \y -> v $$ VPair x y
  PiSwap -> VLam "y" \y -> VLam "x" \x -> v $$ x $$ y
  PiCongL i -> VLam "x" \x -> v $$ transportInv i x
  PiCongR i -> VLam "x" \x -> transport i (v $$ x)
  SigmaCongL i -> transport i (vfst v) `VPair` vsnd v
  SigmaCongR i -> vfst v `VPair` transport i (vsnd v)

-- transport back
transportInv :: Iso -> Value -> Value
transportInv i v = case i of
  Refl -> v
  Sym i -> transport i v
  Trans i j -> transportInv i (transportInv j v)
  Assoc -> (vfst v `VPair` vfst (vsnd v)) `VPair` vsnd (vsnd v)
  Comm -> vsnd v `VPair` vfst v
  SigmaSwap -> vfst (vsnd v) `VPair` (vfst v `VPair` vsnd (vsnd v))
  Curry -> VLam "p" \p -> v $$ vfst p $$ vsnd p
  PiSwap -> VLam "x" \x -> VLam "y" \y -> v $$ y $$ x
  PiCongL i -> VLam "x" \x -> v $$ transport i x
  PiCongR i -> VLam "x" \x -> transportInv i (v $$ x)
  SigmaCongL i -> transportInv i (vfst v) `VPair` vsnd v
  SigmaCongR i -> vfst v `VPair` transportInv i (vsnd v)

--------------------------------------------------------------------------------
-- Type normalisation

data Quant = Quant Name Value (Value -> Value)

-- | curry until the first domain becomes non-sigma
curry :: Quant -> (Quant, Iso)
curry = go Refl
  where
    go i = \case
      Quant x (VSigma y a b) c ->
        go (i <> Curry) $ Quant y a \ ~u -> VPi x (b u) \ ~v -> c (VPair u v)
      t -> (t, i)

-- | associate until the first projection becomes non-sigma
assoc :: Quant -> (Quant, Iso)
assoc = go Refl
  where
    go i = \case
      Quant x (VSigma y a b) c ->
        go (i <> Assoc) $ Quant y a \ ~u -> VSigma x (b u) \ ~v -> c (VPair u v)
      t -> (t, i)

normalise0 :: Term -> (Term, Iso)
normalise0 t = normalise 0 (eval [] t)

normalise :: Level -> Value -> (Term, Iso)
normalise l = \case
  VPi x a b -> normalisePi l (Quant x a b)
  VSigma x a b -> normaliseSigma l (Quant x a b)
  v -> quote l v // mempty

normalisePi :: Level -> Quant -> (Term, Iso)
normalisePi l q = do
  let (Quant x a b, i) = curry q
      (ta, ia) = normalise l a
      (tb, ib) = normalise (l + 1) (b $ transportInv ia (VVar l))
  Pi x ta tb // i <> piCongL ia <> piCongR ib

normaliseSigma :: Level -> Quant -> (Term, Iso)
normaliseSigma l q = do
  let (Quant x a b, i) = assoc q
      (ta, ia) = normalise l a
      (tb, ib) = normalise (l + 1) (b $ transportInv ia (VVar l))
  Sigma x ta tb // i <> sigmaCongL ia <> sigmaCongR ib

--------------------------------------------------------------------------------
-- Conversion modulo isomorphism

dependsOnLevelsBetween :: Level -> Level -> Value -> Bool
dependsOnLevelsBetween from to = go to
  where
    go l = \case
      VRigid x sp -> (from <= x && x <= to) || goSpine l sp
      VTop _ sp -> goSpine l sp
      VU -> False
      VPi _ a b -> go l a || goBind l b
      VLam _ t -> goBind l t
      VSigma _ a b -> go l a || goBind l b
      VPair t u -> go l t || go l u

    goBind l t = go (l + 1) (t $ VVar l)

    goSpine l = \case
      SNil -> False
      SApp sp t -> goSpine l sp || go l t
      SFst sp -> goSpine l sp
      SSnd sp -> goSpine l sp

instantiatePiAt :: Int -> Value -> Value -> Value
instantiatePiAt = \cases
  i ~_ _ | i < 0 -> error "instantiatePiAt: negative index"
  0 ~v (VPi _ _ b) -> b v
  i ~v (VPi x a b) -> VPi x a (instantiatePiAt (i - 1) v . b)
  _ ~_ _ -> error "instantiatePiAt: not a pi"

-- NOTE: This may make the first domain a sigma type
pickDomain :: Level -> Quant -> [(Quant, Iso)]
pickDomain l q@(Quant x a b) = (q, Refl) : go l b
  where
    go l' c = case c (VVar l') of
      VPi _ c1 c2
        | dependsOnLevelsBetween l l' c1 -> go (l' + 1) c2
      VPi y c1 c2 -> do
        let i = coerce (l' - l)
            rest ~vc1 = VPi x a (instantiatePiAt i vc1 . b)
            s = swaps i
        (Quant y c1 rest, s) : go (l' + 1) c2
      _ -> []

    swaps = \case
      (0 :: Int) -> PiSwap
      n -> piCongR (swaps (n - 1)) <> PiSwap

-- | curry and pickDomain combined
-- guaranteed that the first domain is non-sigma
currySwap :: Level -> Quant -> [(Quant, Iso)]
currySwap l q = do
  (q, i) <- pure $ curry q
  (q, j) <- pickDomain l q
  (q, k) <- pure $ curry q
  pure $! q // i <> j <> k

instantiateSigmaAt :: Int -> Value -> Value -> Value
instantiateSigmaAt = \cases
  i ~_ _ | i < 0 -> error "instantiateSigmaAt: negative index"
  0 ~v (VSigma _ _ b) -> b v
  i ~v (VSigma x a b) -> VSigma x a (instantiateSigmaAt (i - 1) v . b)
  _ ~_ _ -> error "instantiateSigmaAt: not a sigma"

dropLastProjection :: Level -> Value -> Value
dropLastProjection l = \case
  VSigma x a b -> case b (VVar l) of
    VSigma {} -> VSigma x a (dropLastProjection (l + 1) . b)
    _ -> a
  _ -> error "dropLastProjection: not a sigma"

-- NOTE: This may make the first projection a sigma type
pickProjection :: Level -> Quant -> [(Quant, Iso)]
pickProjection l q@(Quant x a b) = (q, Refl) : go l b
  where
    go l' c = case c (VVar l') of
      VSigma _ c1 c2
        | dependsOnLevelsBetween l l' c1 -> go (l' + 1) c2
      VSigma y c1 c2 -> do
        let i = coerce (l' - l)
            rest ~vc1 = VSigma x a (instantiateSigmaAt i vc1 . b)
            s = swaps SigmaSwap i
        (Quant y c1 rest, s) : go (l' + 1) c2
      c' | dependsOnLevelsBetween l l' c' -> []
      c' -> do
        let rest ~_ = dropLastProjection l' (VSigma x a b)
            s = swaps Comm (coerce $ l' - l)
        [(Quant "_" c' rest, s)]

    swaps i = \case
      (0 :: Int) -> i
      n -> sigmaCongR (swaps i (n - 1)) <> SigmaSwap

-- | assoc and pickProjection combined
-- guaranteed that the first projection is non-sigma
assocSwap :: Level -> Quant -> [(Quant, Iso)]
assocSwap l q = do
  (q, i) <- pure $ assoc q
  (q, j) <- pickProjection l q
  (q, k) <- pure $ assoc q
  pure $! q // i <> j <> k

convIso0 :: (MonadPlus m) => Term -> Term -> m Iso
convIso0 t u = do
  (i, j) <- convIso 3 0 (eval [] t) (eval [] u)
  pure $! i <> sym j

convIso :: (MonadPlus m) => Int -> Level -> Value -> Value -> m (Iso, Iso)
convIso fuel l = \cases
  -- pi is only convertible with pi under the isomorphisms we consider here
  (VPi x a b) (VPi x' a' b') -> convPi fuel l (Quant x a b) (Quant x' a' b')
  (VPi {}) _ -> empty
  _ (VPi {}) -> empty
  -- likewise
  (VSigma x a b) (VSigma x' a' b') -> convSigma fuel l (Quant x a b) (Quant x' a' b')
  (VSigma {}) _ -> empty
  _ (VSigma {}) -> empty
  t u -> (Refl, Refl) <$ guard (conv l t u)

convPi :: (MonadPlus m) => Int -> Level -> Quant -> Quant -> m (Iso, Iso)
convPi fuel l q q' = do
  let (Quant _ a b, i) = curry q
  flip (parFoldMapA fuel rseq) (currySwap l q') \(Quant _ a' b', i') -> do
    (ia, ia') <- convIso (fuel - 1) l a a'
    let v = transportInv ia (VVar l)
        v' = transportInv ia' (VVar l)
    (ib, ib') <- convIso (fuel - 1) (l + 1) (b v) (b' v')
    pure $! i <> piCongL ia <> piCongR ib // i' <> piCongL ia' <> piCongR ib'

convSigma :: (MonadPlus m) => Int -> Level -> Quant -> Quant -> m (Iso, Iso)
convSigma fuel l q q' = do
  let (Quant _ a b, i) = assoc q
  flip (parFoldMapA fuel rseq) (assocSwap l q') \(Quant _ a' b', i') -> do
    (ia, ia') <- convIso (fuel - 1) l a a'
    let v = transportInv ia (VVar l)
        v' = transportInv ia' (VVar l)
    (ib, ib') <- convIso (fuel - 1) (l + 1) (b v) (b' v')
    pure $! i <> sigmaCongL ia <> sigmaCongR ib // i' <> sigmaCongL ia' <> sigmaCongR ib'

--------------------------------------------------------------------------------
-- Type normalisation + Permutation

normalisePermute0 :: Term -> [(Term, Iso)]
normalisePermute0 t = normalisePermute 0 (eval [] t)

normalisePermute :: Level -> Value -> [(Term, Iso)]
normalisePermute l = \case
  VPi x a b -> normalisePermutePi l (Quant x a b)
  VSigma x a b -> normalisePermuteSigma l (Quant x a b)
  v -> pure (quote l v, Refl)

normalisePermutePi :: Level -> Quant -> [(Term, Iso)]
normalisePermutePi l q = do
  (Quant x a b, i) <- currySwap l q
  (a, ia) <- normalisePermute l a
  let v = transportInv ia (VVar l)
  (b, ib) <- normalisePermute (l + 1) (b v)
  pure $! Pi x a b // i <> piCongL ia <> piCongR ib

normalisePermuteSigma :: Level -> Quant -> [(Term, Iso)]
normalisePermuteSigma l q = do
  (Quant x a b, i) <- assocSwap l q
  (a, ia) <- normalisePermute l a
  let v = transportInv ia (VVar l)
  (b, ib) <- normalisePermute (l + 1) (b v)
  pure $! Sigma x a b // i <> sigmaCongL ia <> sigmaCongR ib

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

prettyTerm0 :: Term -> String
prettyTerm0 t = prettyTerm [] 0 t ""

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

prettyIso0 :: Iso -> String
prettyIso0 i = prettyIso 0 i ""

prettyIso :: Int -> Iso -> ShowS
prettyIso p = \case
  Refl -> showString "refl"
  Sym i -> par p 11 $ prettyIso 12 i . showString " ⁻¹"
  Trans i j -> par p 9 $ prettyIso 9 i . showString " · " . prettyIso 9 j
  Assoc -> showString "Assoc"
  Comm -> showString "Comm"
  SigmaSwap -> showString "ΣSwap"
  Curry -> showString "Curry"
  PiSwap -> showString "ΠSwap"
  PiCongL i -> par p 10 $ showString "ΠL " . prettyIso 11 i
  PiCongR i -> par p 10 $ showString "ΠR " . prettyIso 11 i
  SigmaCongL i -> par p 10 $ showString "ΣL " . prettyIso 11 i
  SigmaCongR i -> par p 10 $ showString "ΣR " . prettyIso 11 i
