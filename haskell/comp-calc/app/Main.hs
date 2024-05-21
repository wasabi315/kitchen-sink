-- Ref: https://github.com/pa-ba/calc-graph-comp

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Strict #-}

import Control.Monad.State
import Data.Functor
import GHC.TypeNats

main = putStrLn $ pretty $ gcompile expr

--------------------------------------------------------------------------------

data Partial a
  = Now a
  | Later ~(Partial a)
  deriving (Eq, Show)

never :: Partial a
never = Later never

force :: Partial a -> a
force (Now x) = x
force (Later p) = force p

deriving instance Functor Partial

instance Applicative Partial where
  pure = Now
  Now f <*> m = f <$> m
  Later mf <*> m = Later (mf <*> m)

instance Monad Partial where
  Now x >>= f = f x
  Later m >>= f = Later (m >>= f)

infix 4 `bisim`

bisim :: (Eq a) => Partial a -> Partial a -> Partial Bool
Now x `bisim` Now y = pure (x == y)
Later m `bisim` Later n = Later (m `bisim` n)
_ `bisim` _ = pure False

--------------------------------------------------------------------------------

infixl 6 :+

data Expr
  = Val Int
  | Expr :+ Expr
  | Get
  | Put Expr Expr
  | While Expr Expr
  deriving (Show)

expr :: Expr
expr = Put (Val 10) (While Get (Put (Get :+ Val (-1)) Get))

eval :: Expr -> Int -> Partial (Int, Int)
eval (Val n) q = pure (n, q)
eval (x :+ y) q = do
  (m, q1) <- eval x q
  (n, q2) <- eval y q1
  return (m + n, q2)
eval Get q = return (q, q)
eval (Put x y) q = do
  (n, _) <- eval x q
  eval y n
eval (While x y) q = do
  (n, q1) <- eval x q
  if n == 0
    then return (0, q1)
    else do
      (_, q2) <- eval y q1
      Later (eval (While x y) q2)

--------------------------------------------------------------------------------

infixr 4 :>

data Vec (n :: Nat) a where
  Nil :: Vec 0 a
  (:>) :: a -> Vec n a -> Vec (n + 1) a

deriving instance (Show a) => Show (Vec n a)

deriving instance Functor (Vec n)

--------------------------------------------------------------------------------

infixr 4 `GSeq`

data CFG l t i
  = i `GSeq` CFG l t i
  | forall n. GTerm (t n) (Vec n l)
  | GLab (l -> CFG l t i) (l -> CFG l t i)

deriving instance Functor (CFG l t)

data Tree t i
  = i `TSeq` Tree t i
  | forall n. TBranch (t n) (Vec n (Tree t i))
  | TRec ~(Tree t i)

deriving instance Functor (Tree t)

deriving instance (forall n. Show (t n), Show i) => Show (Tree t i)

unlabel :: CFG (Tree t i) t i -> Tree t i
unlabel (i `GSeq` g) = i `TSeq` unlabel g
unlabel (GTerm t ts) = TBranch t ts
unlabel (GLab f g) = unlabel $ f $ fix \ ~c -> unlabel $ g $ TRec c

--------------------------------------------------------------------------------

data Instr
  = Push Int
  | Add
  | Store
  | Load
  | Pop
  deriving (Show)

data Term n where
  Halt :: Term 0
  Jpz :: Term 2
  Jmp :: Term 1

deriving instance Show (Term n)

--------------------------------------------------------------------------------

type TCode = Tree Term Instr

pattern TPush :: Int -> TCode -> TCode
pattern TPush n c = Push n `TSeq` c

pattern TAdd, TStore, TLoad, TPop :: TCode -> TCode
pattern TAdd c = Add `TSeq` c
pattern TStore c = Store `TSeq` c
pattern TLoad c = Load `TSeq` c
pattern TPop c = Pop `TSeq` c

pattern THalt :: TCode
pattern THalt = TBranch Halt Nil

pattern TJpz :: TCode -> TCode -> TCode
pattern TJpz cz cnz = TBranch Jpz (cz :> cnz :> Nil)

pattern TJmp :: TCode -> TCode
pattern TJmp c = TBranch Jmp (c :> Nil)

{-# COMPLETE TPush, TAdd, TStore, TLoad, TPop, THalt, TJmp, TJpz, TRec #-}

tcomp :: Expr -> TCode -> TCode
tcomp (Val n) c = TPush n c
tcomp (x :+ y) c = tcomp x $ tcomp y $ TAdd c
tcomp Get c = TLoad c
tcomp (Put x y) c = tcomp x $ TStore $ tcomp y c
tcomp (While x y) c = fix \ ~c' -> tcomp x $ TJpz c $ tcomp y $ TPop $ TRec c'

tcompile :: Expr -> TCode
tcompile e = tcomp e THalt

texec :: TCode -> ([Int], Int) -> Partial ([Int], Int)
texec THalt conf = return conf
texec (TPush n c) (s, q) = texec c (n : s, q)
texec (TAdd c) (m : n : s, q) = texec c ((n + m) : s, q)
texec (TLoad c) (s, q) = texec c (q : s, q)
texec (TStore c) (n : s, _) = texec c (s, n)
texec (TPop c) (_ : s, q) = texec c (s, q)
texec (TJmp c) conf = texec c conf
texec (TJpz c' c) (n : s, q) = if n == 0 then texec c' (0 : s, q) else texec c (s, q)
texec (TRec c) conf = Later (texec c conf)
texec _ _ = return ([], 0)

--------------------------------------------------------------------------------

type GCode l = CFG l Term Instr

pattern GPush :: Int -> GCode l -> GCode l
pattern GPush n c = Push n `GSeq` c

pattern GAdd, GStore, GLoad, GPop :: GCode l -> GCode l
pattern GAdd c = Add `GSeq` c
pattern GStore c = Store `GSeq` c
pattern GLoad c = Load `GSeq` c
pattern GPop c = Pop `GSeq` c

pattern GHalt :: GCode l
pattern GHalt = GTerm Halt Nil

pattern GJmp :: l -> GCode l
pattern GJmp l = GTerm Jmp (l :> Nil)

pattern GJpz :: l -> l -> GCode l
pattern GJpz l1 l2 = GTerm Jpz (l1 :> l2 :> Nil)

{-# COMPLETE GPush, GAdd, GStore, GLoad, GPop, GHalt, GJmp, GJpz, GLab #-}

gcomp :: Expr -> GCode l -> GCode l
gcomp (Val n) c = GPush n c
gcomp (x :+ y) c = gcomp x $ gcomp y $ GAdd c
gcomp Get c = GLoad c
gcomp (Put x y) c = gcomp x $ GStore $ gcomp y c
gcomp (While x y) c =
  GLab GJmp \l1 ->
      do
        \l3 ->
            do \l2 -> gcomp x $ GJpz l3 l2
          `GLab`
            do \_ -> gcomp y $ GPop $ GJmp l1
    `GLab`
      do \_ -> c

gcompile :: Expr -> GCode l
gcompile e = gcomp e GHalt

gexec :: (forall l. GCode l) -> ([Int], Int) -> Partial ([Int], Int)
gexec c s = texec (unlabel c) s

pretty :: (forall l. GCode l) -> String
pretty c = evalState (go c) 0 ""
  where
    go :: GCode Int -> State Int ShowS
    go GHalt = return $ showString "  halt"
    go (GPush n c) = go c <&> \f -> showString "  push " . shows n . showChar '\n' . f
    go (GAdd c) = (showString "  add\n" .) <$> go c
    go (GLoad c) = (showString "  load\n" .) <$> go c
    go (GStore c) = (showString "  store\n" .) <$> go c
    go (GPop c) = (showString "  pop\n" .) <$> go c
    go (GJpz lz lnz) = return $ showString "  jpz Lbl" . shows lz . showString " Lbl" . shows lnz . showChar '\n'
    go (GJmp l) = return (showString "  jmp Lbl" . shows l . showChar '\n')
    go (GLab f g) = do
      l <- get
      put (succ l)
      (\s t -> s . showString "Lbl" . shows l . showString ":\n" . t) <$> go (f l) <*> go (g l)
