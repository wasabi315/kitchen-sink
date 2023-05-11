{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Monad.State
import Data.Data
import Data.Generics.Uniplate.Data
import Data.Map.Strict qualified as Map
import Data.String

newtype Var = Name String
  deriving stock (Eq, Data, Typeable)
  deriving newtype (Show, IsString)

data Expr
  = Lit Int
  | Var Var
  | Neg Expr
  | Expr :+ Expr
  deriving stock (Eq, Show, Data, Typeable)

data Stmt
  = Var := Expr
  | Print Expr
  deriving stock (Eq, Show, Data, Typeable)

infix 0 :=

infixl 6 :+

data Env = Env
  { count :: Int,
    table :: Map.Map String String
  }

initEnv :: Env
initEnv = Env 0 Map.empty

rename :: Biplate a Var => a -> a
rename =
  (`evalState` initEnv) . transformBiM \(Name name) -> do
    Env {count, table} <- get
    case Map.lookup name table of
      Just name' -> pure $ Name name'
      Nothing -> do
        let name' = 'v' : show count
            count' = count + 1
            table' = Map.insert name name' table
        put Env {count = count', table = table'}
        pure $ Name name'

negLits :: Biplate a Expr => a -> a
negLits =
  transformBi \case
    Neg (Lit i) -> Lit $ negate i
    x -> x

transformPasses :: [Stmt] -> [Stmt]
transformPasses = negLits . rename

testStmts :: [Stmt]
testStmts =
  [ "x" := Lit 0,
    "y" := Neg (Lit 1),
    Print $ Var "x" :+ Var "y"
  ]

main :: IO ()
main = do
  print testStmts
  print $ transformPasses testStmts
