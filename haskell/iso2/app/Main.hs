{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

main :: IO ()
main = do
  let t = Pi "F" (Pi "_" (Sigma "_" Type Type) Type) $ Pi "A" Type $ Pi "B" Type $ Var 2 :@ Pair (Var 1) (Var 0)
  putStrLn $ prettyTerm [] 0 t ""
  let (t', i) = nquote 0 $ normalise 0 $ eval [] t
  putStrLn $ prettyTerm [] 0 t' ""
  putStrLn $ prettyIsoCong i ""

--------------------------------------------------------------------------------

type Name = String

newtype Index = Index Int
  deriving newtype (Show, Ord, Eq, Num)

infixl 6 :@

data Term
  = Var Index
  | Type
  | Unit
  | TT
  | Pi Name Term Term
  | Lam Name Term
  | Term :@ Term
  | Sigma Name Term Term
  | Pair Term Term
  | Fst Term
  | Snd Term
  | Eq Term Term Term
  | Sym Term
  deriving (Show)

--------------------------------------------------------------------------------

newtype Level = Level Int
  deriving newtype (Show, Ord, Eq, Num)

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index (l - x - 1)

data Value
  = VRigid Level Spine
  | VType
  | VUnit
  | VTT
  | VPi Name Value (Value -> Value)
  | VAbs Name (Value -> Value)
  | VSigma Name Value (Value -> Value)
  | VPair Value Value
  | VEq Value Value Value

data Spine
  = SNil
  | SApp Spine Value
  | SFst Spine
  | SSnd Spine
  | SSym Spine

type Env = [Value]

eval :: Env -> Term -> Value
eval env = \case
  Var (Index x) -> env !! x
  Type -> VType
  Unit -> VUnit
  TT -> VTT
  Pi x a b -> VPi x (eval env a) \v -> eval (v : env) b
  Lam x t -> VAbs x \v -> eval (v : env) t
  t :@ u -> eval env t `vapp` eval env u
  Sigma x a b -> VSigma x (eval env a) \v -> eval (v : env) b
  Pair a b -> eval env a `VPair` eval env b
  Fst t -> vfst (eval env t)
  Snd t -> vsnd (eval env t)
  Eq a t u -> VEq (eval env a) (eval env t) (eval env u)
  Sym p -> vsym (eval env p)

vapp :: Value -> Value -> Value
vapp = \cases
  (VRigid l sp) u -> VRigid l (SApp sp u)
  (VAbs _ f) u -> f u
  _ _ -> error "vapp: not a function"

vfst :: Value -> Value
vfst = \case
  VRigid l sp -> VRigid l (SFst sp)
  VPair a _ -> a
  _ -> error "vfst: not a pair"

vsnd :: Value -> Value
vsnd = \case
  VRigid l sp -> VRigid l (SSnd sp)
  VPair _ b -> b
  _ -> error "vsnd: not a pair"

vsym :: Value -> Value
vsym = \case
  VRigid l (SSym sp) -> VRigid l sp
  VRigid l sp -> VRigid l (SSym sp)
  _ -> error "vsym: not an equality"

quote :: Level -> Value -> Term
quote l = \case
  VRigid x sp -> quoteSpine l (Var $ levelToIndex l x) sp
  VType -> Type
  VUnit -> Unit
  VTT -> TT
  VPi x a b -> Pi x (quote l a) (quote (l + 1) $ b $ VRigid l SNil)
  VAbs x t -> Lam x $ quote (l + 1) $ t $ VRigid l SNil
  VSigma x a b -> Sigma x (quote l a) (quote (l + 1) $ b $ VRigid l SNil)
  VPair t u -> Pair (quote l t) (quote l u)
  VEq a t u -> Eq (quote l a) (quote l t) (quote l u)

quoteSpine :: Level -> Term -> Spine -> Term
quoteSpine lvl hd = \case
  SNil -> hd
  SApp sp t -> quoteSpine lvl hd sp :@ quote lvl t
  SFst sp -> Fst $ quoteSpine lvl hd sp
  SSnd sp -> Snd $ quoteSpine lvl hd sp
  SSym sp -> Sym $ quoteSpine lvl hd sp

--------------------------------------------------------------------------------
-- Isomorphisms

data EquivClosure r
  = Refl
  | EquivClosure r `Trans` r
  | EquivClosure r `SymTrans` r
  deriving (Show, Functor)

instance Semigroup (EquivClosure r) where
  r1 <> Refl = r1
  r1 <> (r2 `Trans` r3) = (r1 <> r2) `Trans` r3
  r1 <> (r2 `SymTrans` r3) = (r1 <> r2) `SymTrans` r3

instance Monoid (EquivClosure r) where
  mempty = Refl

type Iso = EquivClosure Iso'

data Iso'
  = -- | (x : (y : A) * B[y]) * C[x] ~ (x : A) * (y : B[x]) * C[(x, y)]
    SigmaAssoc
  | -- | (x : A) * B ~ (x : B) * A
    SigmaComm
  | -- | (x : (y : A) * B[y]) -> C[x] ~ (x : A) (y : B[x]) -> C[(x, y)]
    Curry
  | -- (x : Unit) * A[x] ~ A[tt]
    SigmaUnitL
  | -- | (x : A) * Unit ~ A
    SigmaUnitR
  | -- | (x : Unit) -> A[x] ~ A[tt]
    PiUnitL
  | -- | Eq A t u ~ Eq A u t
    EqComm
  deriving (Show)

type IsoCong = EquivClosure IsoCong'

data IsoCong'
  = Iso Iso'
  | -- | (iso : A ~ A') => ((x : A) -> B[x]) ~ ((x : A') -> B[iso.from x])
    PiCongL IsoCong'
  | -- | B[x] ~ B'[x] => ((x : A) -> B[x]) ~ ((x : A) -> B'[x])
    PiCongR IsoCong'
  | -- | (iso : A ~ A') => ((x : A) * B[x]) ~ ((x : A') * B[iso.from x])
    SigmaCongL IsoCong'
  | -- | B[x] ~ B'[x] => ((x : A) * B[x]) ~ ((x : A) * B'[x])
    SigmaCongR IsoCong'
  deriving (Show)

class ToFrom r where
  to :: r -> Value -> Value
  from :: r -> Value -> Value

instance ToFrom Iso' where
  to i t = case i of
    SigmaAssoc -> vfst (vfst t) `VPair` (vsnd (vfst t) `VPair` vsnd t)
    SigmaComm -> vsnd t `VPair` vfst t
    Curry -> VAbs "u" \u -> VAbs "v" \v -> t `vapp` (u `VPair` v)
    SigmaUnitL -> vsnd t
    SigmaUnitR -> vfst t
    PiUnitL -> t `vapp` VTT
    EqComm -> vsym t

  from i t = case i of
    SigmaAssoc -> (vfst t `VPair` vfst (vsnd t)) `VPair` vsnd (vsnd t)
    SigmaComm -> vsnd t `VPair` vfst t
    Curry -> VAbs "u" \u -> (t `vapp` vfst u) `vapp` vsnd u
    SigmaUnitL -> VPair VUnit t
    SigmaUnitR -> VPair t VUnit
    PiUnitL -> VAbs "u" \_ -> t
    EqComm -> vsym t

instance ToFrom IsoCong' where
  to i t = case i of
    Iso j -> to j t
    PiCongL j -> VAbs "u" \u -> t `vapp` from j u
    PiCongR j -> VAbs "v" \u -> to j (t `vapp` u)
    SigmaCongL j -> to j (vfst t) `VPair` vsnd t
    SigmaCongR j -> vfst t `VPair` to j (vsnd t)

  from i t = case i of
    Iso j -> from j t
    PiCongL j -> VAbs "u" \u -> t `vapp` to j u
    PiCongR j -> VAbs "v" \u -> from j (t `vapp` u)
    SigmaCongL j -> from j (vfst t) `VPair` vsnd t
    SigmaCongR j -> vfst t `VPair` from j (vsnd t)

instance (ToFrom r) => ToFrom (EquivClosure r) where
  to i t = case i of
    Refl -> t
    Trans j k -> to k (to j t)
    SymTrans j k -> to k (from j t)

  from i t = case i of
    Refl -> t
    Trans j k -> from j (from k t)
    SymTrans j k -> to j (from k t)

class PiSigmaCong r s where
  piCongL :: r -> s
  piCongR :: r -> s
  sigmaCongL :: r -> s
  sigmaCongR :: r -> s

instance PiSigmaCong Iso' IsoCong' where
  piCongL = piCongL . Iso
  piCongR = piCongR . Iso
  sigmaCongL = sigmaCongL . Iso
  sigmaCongR = sigmaCongR . Iso

instance PiSigmaCong IsoCong' IsoCong' where
  piCongL = PiCongL
  piCongR = PiCongR
  sigmaCongL = SigmaCongL
  sigmaCongR = SigmaCongR

instance (PiSigmaCong r s) => PiSigmaCong (EquivClosure r) (EquivClosure s) where
  piCongL = fmap piCongL
  piCongR = fmap piCongR
  sigmaCongL = fmap sigmaCongL
  sigmaCongR = fmap sigmaCongR

--------------------------------------------------------------------------------
-- Normalise

type NValue = (NValue', Iso)

data NValue'
  = NRigid Level Spine
  | NType
  | NUnit
  | NTT
  | NPi Name NValue (Value -> NValue)
  | NAbs Name (Value -> Value)
  | NSigma Name NValue (Value -> NValue)
  | NPair Value Value
  | NEq Value Value Value

normalise :: Level -> Value -> NValue
normalise = go Refl
  where
    go acc l = \case
      VSigma n (VSigma m a b) c ->
        go (acc `Trans` SigmaAssoc) l $ VSigma n a \x -> VSigma m (b x) \y -> c (VPair x y)
      VPi n (VSigma m a b) c ->
        go (acc `Trans` Curry) l $ VPi n a \x -> VPi m (b x) \y -> c (VPair x y)
      VSigma _ VUnit b ->
        go (acc `Trans` SigmaUnitL) l $ b VTT
      VSigma _ a (($ VRigid l SNil) -> VUnit) ->
        go (acc `Trans` SigmaUnitR) l $ a
      VPi _ VUnit b ->
        go (acc `Trans` PiUnitL) l $ b VTT
      VSigma x a b ->
        let a' = go Refl l a
            t = NSigma x a' (go Refl (l + 1) . b . from (snd a'))
         in (t, acc)
      VPi x a b ->
        let a' = go Refl l a
            t = NPi x a' (go Refl (l + 1) . b . from (snd a'))
         in (t, acc)
      VType -> (NType, acc)
      VRigid x sp -> (NRigid x sp, acc)
      VAbs x f -> (NAbs x f, acc)
      VPair t u -> (NPair t u, acc)
      VUnit -> (NUnit, acc)
      VTT -> (NTT, acc)
      VEq a t u -> (NEq a t u, acc)

nquote :: Level -> NValue -> (Term, IsoCong)
nquote l = \case
  (NRigid x sp, i) ->
    let t = quoteSpine l (Var $ levelToIndex l x) sp
        i' = fmap Iso i
     in (t, i')
  (NType, i) ->
    let i' = fmap Iso i
     in (Type, i')
  (NUnit, i) ->
    let i' = fmap Iso i
     in (Unit, i')
  (NTT, i) ->
    let i' = fmap Iso i
     in (TT, i')
  (NPi x a b, i) ->
    let (a', j) = nquote l a
        (b', k) = nquote (l + 1) $ b (VRigid l SNil)
        i' = fmap Iso i <> piCongL j <> piCongR k
     in (Pi x a' b', i')
  (NAbs x t, i) ->
    let t' = quote (l + 1) $ t (VRigid l SNil)
        i' = fmap Iso i
     in (Lam x t', i')
  (NSigma x a b, i) ->
    let (a', j) = nquote l a
        (b', k) = nquote (l + 1) $ b (VRigid l SNil)
        i' = fmap Iso i <> piCongL j <> piCongR k
     in (Sigma x a' b', i')
  (NPair t u, i) ->
    let t' = quote l t
        u' = quote l u
        i' = fmap Iso i
     in (Pair t' u', i')
  (NEq a t u, i) ->
    let a' = quote l a
        t' = quote l t
        u' = quote l u
        i' = fmap Iso i
     in (Eq a' t' u', i')

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
      Type -> showString "Type"
      Pi "_" a b ->
        par p piP $ go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        par p piP $ piBind n ns a . goPi (n : ns) b
      Lam (freshen ns -> n) t ->
        par p absP $
          showString "λ " . shows n . goAbs (n : ns) t
      t :@ u -> par p appP $ go ns appP t . showChar ' ' . go ns projP u
      Sigma "_" a b ->
        par p sigmaP $ go ns appP a . showString " × " . go ("_" : ns) sigmaP b
      Sigma (freshen ns -> n) a b ->
        par p sigmaP $ piBind n ns a . showString " × " . go (n : ns) sigmaP b
      Fst t -> par p projP $ go ns projP t . showString ".1"
      Snd t -> par p projP $ go ns projP t . showString ".2"
      Pair t u -> par p pairP $ go ns absP t . showString " , " . go ns pairP u
      Unit -> showString "Unit"
      TT -> showString "tt"
      Eq a t u -> showString "Eq " . go ns projP a . showChar ' ' . go ns projP t . showChar ' ' . go ns projP u
      Sym t -> showString "sym " . go ns projP t

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
        showChar ' ' . shows n . goAbs (n : ns) t
      t -> showString ". " . go ns absP t

prettyIso' :: Iso' -> ShowS
prettyIso' =
  showString . \case
    SigmaAssoc -> "ΣAssoc"
    SigmaComm -> "ΣComm"
    Curry -> "Curry"
    SigmaUnitL -> "ΣUnitL"
    SigmaUnitR -> "ΣUnitR"
    PiUnitL -> "ΠUnitL"
    EqComm -> "=Comm"

prettyIsoCong' :: Int -> IsoCong' -> ShowS
prettyIsoCong' p = \case
  Iso i -> prettyIso' i
  PiCongL i -> par p 10 $ showString "ΠL " . prettyIsoCong' 11 i
  PiCongR i -> par p 10 $ showString "ΠR " . prettyIsoCong' 11 i
  SigmaCongL i -> par p 10 $ showString "ΣL " . prettyIsoCong' 11 i
  SigmaCongR i -> par p 10 $ showString "ΣR " . prettyIsoCong' 11 i

prettyEquivClosure :: (r -> ShowS) -> EquivClosure r -> ShowS
prettyEquivClosure f = \case
  Refl -> showString "refl"
  (Refl `Trans` r) -> f r
  (Refl `SymTrans` r) -> f r . showString "⁻¹"
  (rs `Trans` r) -> prettyEquivClosure f rs . showString " · " . f r
  (rs `SymTrans` r) -> prettyEquivClosure f rs . showString " · " . f r . showString "⁻¹"

prettyIso :: Iso -> ShowS
prettyIso = prettyEquivClosure prettyIso'

prettyIsoCong :: IsoCong -> ShowS
prettyIsoCong = prettyEquivClosure (prettyIsoCong' 0)
