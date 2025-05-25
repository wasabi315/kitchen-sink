-- References:
--   - McBride 2018 Everybody's Got To Be Somewhere
--   - https://github.com/pigworker/LEOG
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

import Data.Bits
import Data.Bits.Pdep
import Data.Bits.Pext
import Data.Word

main :: IO ()
main = do
  let _3p5 = plus `app` church 3 `app` church 5
      _8 = church 8
  putStrLn $ "3 + 5           : " ++ prettyTerm 0 0 _3p5 ""
  putStrLn $ "nf(3 + 5)       : " ++ prettyTerm 0 0 (nf ENil _3p5) ""
  putStrLn $ "8               : " ++ prettyTerm 0 0 _8 ""
  putStrLn $ "nf(3 + 5) =?= 8 : " ++ show (nf ENil _3p5 == _8)

--------------------------------------------------------------------------------

-- Thinnings
-- The i-th least significant bit may mask the i-th nearest variable in scope.
-- Only 64 variables are supported in this implementation.
newtype Thin = Thin Word64
  deriving (Eq, Show)

srcSize :: Thin {-m,n-} -> Int {-m-}
srcSize (Thin t) = popCount t

zeroThin :: Thin {-0,m-}
zeroThin = Thin 0

idThin :: Thin {-m,m-}
idThin = Thin oneBits

-- de Bruijn index is a singleton thinning
singletonThin :: Int -> Thin
singletonThin i = Thin (bit i)

compThin :: Thin {-m,n-} -> Thin {-n,o-} -> Thin {-m,o-}
compThin (Thin t) (Thin u) = Thin (pdep t u)

snoc :: Thin -> Bool -> Thin
snoc (Thin t) b = Thin (2 * t + if b then 1 else 0)

unsnoc :: Thin -> (Thin, Bool)
unsnoc (Thin t) = case t `divMod` 2 of
  (t', b) -> (Thin t', b /= 0)

pattern (:>) :: Thin -> Bool -> Thin
pattern t :> b <- (unsnoc -> (t, b)) where t :> b = snoc t b

{-# COMPLETE (:>) #-}

instance Semigroup Thin where
  (<>) = compThin

instance Monoid Thin where
  mempty = idThin

coprod :: Thin {-i,m-} -> Thin {-j,m-} -> (Thin {-i,n-}, Thin {-j,n-}, Thin {-n,m-})
coprod (Thin t) (Thin u) = (Thin t', Thin u', Thin v)
  where
    !v = t .|. u
    !t' = pext t v
    !u' = pext u v

data Thinned a = a :^ Thin
  deriving (Eq, Show)

thinMore :: Thin -> Thinned a -> Thinned a
thinMore t (a :^ u) = a :^ (u <> t)

--------------------------------------------------------------------------------

data Term'
  = Var
  | Lam Bool Term'
  | App Thin Term' Thin Term' -- Two thinnings form a cover
  deriving (Eq, Show)

-- Lambda terms with co-de Bruijn indices
type Term = Thinned Term'

var :: Int -> Term
var i = Var :^ singletonThin i

lam :: Term -> Term
lam (l :^ (t :> b)) = Lam b l :^ t

app :: Term -> Term -> Term
app (l :^ t) (m :^ u) = case coprod t u of
  (t', u', v) -> App t' l u' m :^ v

--------------------------------------------------------------------------------

data Value'
  = VLam Closure
  | VRigid Spine
  deriving (Eq, Show)

data Spine
  = SNil {-1-}
  | SApp Thin Spine Thin Value'
  deriving (Eq, Show)

data Closure = Closure Thin Env Bool Term'
  deriving (Eq, Show)

type Value = Thinned Value'

data Env
  = ENil
  | ECons Value Thin Env
  deriving (Eq, Show)

(!) :: Env -> Thin -> Value
(!) = \xs (Thin t) -> go idThin xs (countTrailingZeros t)
  where
    go t = \cases
      (ECons v _ _) 0 -> thinMore t v
      (ECons _ u xs) d -> go (u <> t) xs (d - 1)
      ENil _ -> error "Variable not found"

thinEnv :: Thin -> Env -> Env
thinEnv t = \case
  ENil -> ENil
  ECons v u xs -> ECons (thinMore t v) (u <> t) xs

eval :: Env -> Term -> Value
eval env = \case
  Var :^ t -> env ! t
  Lam b u :^ t -> VLam (Closure t env b u) :^ idThin
  App t l u m :^ v ->
    eval env (l :^ (t <> v)) `vapp` eval env (m :^ (u <> v))

capp :: Thinned Closure -> Value -> Value
capp = \cases
  (Closure t env True l :^ u) m ->
    eval (ECons m u env) (l :^ (t :> True))
  (Closure t env False l :^ u) _ ->
    eval (thinEnv u env) (l :^ t)

vapp :: Value -> Value -> Value
vapp = \cases
  (VRigid sp :^ t) (l :^ u) -> case coprod t u of
    (t', u', v) -> VRigid (SApp t' sp u' l) :^ v
  (VLam c :^ t) m -> capp (c :^ t) m

quote :: Value -> Term
quote = \case
  VLam c :^ t -> lam $ quote $ (c :^ (t :> False)) `capp` (VRigid SNil :^ singletonThin 0)
  VRigid sp :^ t -> quoteSpine (sp :^ t)

quoteSpine :: Thinned Spine -> Term
quoteSpine = \case
  SNil :^ v -> Var :^ (singletonThin 0 <> v)
  SApp t sp u l :^ v -> quoteSpine (sp :^ (t <> v)) `app` quote (l :^ (u <> v))

nf :: Env -> Term -> Term
nf env t = quote (eval env t)

--------------------------------------------------------------------------------

prettyThin :: Int -> Thin -> ShowS
prettyThin = \cases
  0 _ -> id
  k (t :> b) -> prettyThin (k - 1) t . showChar (if b then 'K' else 'T')

prettyCover :: Int -> Thin -> Thin -> ShowS
prettyCover = \cases
  0 _ _ -> id
  _ (_ :> False) (_ :> False) -> error "Invalid cover"
  k (t :> True) (u :> False) -> prettyCover (k - 1) t u . showChar 'L'
  k (t :> False) (u :> True) -> prettyCover (k - 1) t u . showChar 'R'
  k (t :> True) (u :> True) -> prettyCover (k - 1) t u . showChar 'B'

prettyTerm' :: Int -> Int -> Term' -> ShowS
prettyTerm' p k = \case
  Var -> showString "v"
  Lam b t ->
    showParen (p > 0) $
      showString (if b then "λ " else "ƛ ")
        . prettyTerm' 0 (k + if b then 1 else 0) t
  App t l u m ->
    showParen (p > 10) $
      showString "app "
        . ( if t == zeroThin && u == zeroThin
              then id
              else prettyCover k t u . showChar ' '
          )
        . prettyTerm' 11 (srcSize t) l
        . showChar ' '
        . prettyTerm' 11 (srcSize u) m

prettyTerm :: Int -> Int -> Term -> ShowS
prettyTerm p k (l :^ t) =
  showParen (p > 10) $
    prettyTerm' (if k == 0 then p else 11) (srcSize t) l
      . if k == 0
        then id
        else showString " ↑ " . prettyThin k t

--------------------------------------------------------------------------------

_I :: Term
_I = lam $ var 0

_K :: Term
_K = lam $ lam $ var 1

_S :: Term
_S = lam $ lam $ lam $ var 2 `app` var 0 `app` (var 1 `app` var 0)

church :: Int -> Term
church = \n -> lam $ lam $ go n
  where
    go :: Int -> Term
    go 0 = var 0
    go n = var 1 `app` go (n - 1)

plus :: Term
plus = lam $ lam $ lam $ lam $ var 3 `app` var 1 `app` (var 2 `app` var 1 `app` var 0)
