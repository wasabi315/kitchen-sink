{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoFieldSelectors #-}

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.Kind
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as M
import Data.Map.Strict qualified as Map
import Data.Monoid
import Data.Proxy
import GHC.Records

type Field :: forall {k}. k -> Type -> Type -> Constraint
type Field x r a = (HasField x r a, SetField x r a)

type SetField :: forall {k}. k -> Type -> Type -> Constraint
class SetField x r a | x r -> a where
  modifyField :: (a -> a) -> r -> r

setField :: forall x r a. SetField x r a => a -> r -> r
setField = modifyField @x . const

type FoldFields :: forall {k}. [k] -> Type -> Constraint
class FoldFields (xs :: [k]) r where
  foldMapFields :: Monoid m => (forall (x :: k) a. Field x r a => Proxy x -> r -> m) -> r -> m

instance FoldFields '[] r where
  foldMapFields _ = mempty

instance (Field x r a, FoldFields xs r) => FoldFields (x ': xs) r where
  foldMapFields f r = f @x Proxy r <> foldMapFields @xs f r

-- restore specified fields in the state after performing m
restore :: forall {k} (xs :: [k]) s m a. (MonadState s m, FoldFields xs s) => m a -> m a
restore m = do
  Endo f <- gets $ foldMapFields @xs \(Proxy :: Proxy x) s ->
    Endo $ setField @x (getField @x s)
  a <- m
  modify f
  pure a

-- Example: Renamer

type Name = String

data Expr
  = Var Name
  | Int Int
  | Expr :+ Expr
  | Expr :* Expr
  deriving (Eq, Show)

data Stmt
  = Name := Expr
  | Name :<- Expr
  | Print Expr
  | Block [Stmt]
  deriving (Eq, Show)

type Renamer = StateT Env (Except Error)

type Error = String

data Env = Env
  { freshCount :: !Int,
    vars :: NE.NonEmpty (M.Map Name Name)
  }

initialEnv :: Env
initialEnv =
  Env
    { freshCount = 0,
      vars = NE.singleton mempty
    }

instance (a ~ Int) => SetField "freshCount" Env a where
  modifyField f r = r {freshCount = f r.freshCount}

instance (a ~ NE.NonEmpty (M.Map Name Name)) => SetField "vars" Env a where
  modifyField f r = r {vars = f r.vars}

addName :: Name -> Renamer Name
addName nm = do
  count <- gets \env -> env.freshCount
  vs NE.:| vss <- gets \env -> env.vars
  let nm' = "v." ++ show count
  let add (Just _) = throwError $ "variable \'" ++ nm ++ "\' is redefined"
      add Nothing = pure $ Just nm'
  vs' <- Map.alterF add nm vs
  modify \env -> env {vars = vs' NE.:| vss, freshCount = count + 1}
  pure nm'

findName :: Name -> Renamer Name
findName nm = do
  mayNm <- gets \env -> asum . fmap (M.!? nm) $ env.vars
  case mayNm of
    Nothing -> throwError $ "variable \'" ++ nm ++ "\' is undefined"
    Just nm' -> pure nm'

withNewScope :: Renamer a -> Renamer a
withNewScope m =
  restore @'["vars"] do
    modify \env -> env {vars = NE.cons mempty env.vars}
    m

renameStmt :: Stmt -> Renamer Stmt
renameStmt (nm := expr) = do
  nm' <- addName nm
  (nm' :=) <$> renameExpr expr
renameStmt (nm :<- expr) = do
  nm' <- findName nm
  (nm' :<-) <$> renameExpr expr
renameStmt (Print expr) =
  Print <$> renameExpr expr
renameStmt (Block stmts) = withNewScope do
  Block <$> mapM renameStmt stmts

renameExpr :: Expr -> Renamer Expr
renameExpr (Var nm) = Var <$> findName nm
renameExpr (Int n) = pure $ Int n
renameExpr (expr1 :+ expr2) = (:+) <$> renameExpr expr1 <*> renameExpr expr2
renameExpr (expr1 :* expr2) = (:*) <$> renameExpr expr1 <*> renameExpr expr2

rename :: Stmt -> Either Error Stmt
rename = runExcept . (`evalStateT` initialEnv) . renameStmt

main :: IO ()
main = do
  let expr =
        Block
          [ "x" := Int 0,
            "y" := Int 1,
            "x" :<- (Var "x" :+ Var "y"),
            Block
              [ "x" := Int 10,
                "x" :<- (Var "x" :* Var "y")
              ],
            Print (Var "x")
          ]
  print expr
  either print print $ rename expr
