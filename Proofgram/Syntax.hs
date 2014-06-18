{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}

module Proofgram.Syntax where

import Control.Lens
import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.List

type Symbol = String

data Term = App Symbol [Term]
          | Var Symbol
          deriving (Eq, Ord)

data Atom = Pred Symbol [Term]
          | Eq [Term]
          deriving (Eq, Ord)

instance Show Term where
    show (App s ts) = s ++ "(" ++ intercalate "," (map show ts) ++ ")"
    show (Var s) = s

instance Show Atom where
    show (Pred s ts) = s ++ "(" ++ intercalate "," (map show ts) ++ ")"
    show (Eq [a,b]) = show a ++ " = " ++ show b

data Formula = And Formula Formula
             | Or Formula Formula
             | Neg Formula
             | Atom Atom
             | T
             | F
             deriving (Eq, Show)

makePrisms ''Term
makePrisms ''Atom
makePrisms ''Formula

predicateArguments :: Lens' Atom [Term]
predicateArguments f (Pred s ts) = Pred s `fmap` f ts
predicateArguments f (Eq ts) = Eq `fmap` f ts

functions :: Traversal' Term Symbol
functions f (App s ts) = App <$> f s <*> traverse (functions f) ts
functions _ (Var s) = pure $ Var s

variables :: Traversal' Term Term
variables f (App s ts) = App s <$> traverse (variables f) ts
variables f (Var s) = f (Var s)

type Path = [Int]

subTermAt :: Path -> Traversal' Term Term
subTermAt [] = id
subTermAt (i:is) = _App . _2 . ix i . subTermAt is

type Subst = [(Symbol, Term)]

(@@) :: Term -> Subst -> Term
term @@ subst = term & variables %~ \(Var s) -> fromMaybe (Var s) (lookup s subst)

(.*.) :: Subst -> Subst -> Subst
s .*. t = [ (d, (Var d @@ s) @@ t) | d <- (s ++ t) ^.. traverse . _1 ]

mgu :: Monad m => Term -> Term -> m Subst
App s ts `mgu` App u vs = do
    when (s /= u) $ fail $ "different function symbols " ++ s ++ " and " ++ u
    foldM unifyArg [] (zip ts vs)
  where
    unifyArg subst (t, v) = do
      newSubst <- (t @@ subst) `mgu` (v @@ subst)
      return $ subst .*. newSubst
Var s `mgu` Var t = return [(s, Var t)]
Var s `mgu` t = do
    when (Var s `elem` (t ^.. variables)) $ fail $ s ++ " occurs in " ++ show t
    return [(s, t)]
t `mgu` Var s = Var s `mgu` t

solve :: Monad m => Term -> Term -> m Subst
App s ts `solve` App u vs = do
    when (s /= u) $ fail $ "different function symbols " ++ s ++ " and " ++ u
    foldM solveArg [] (zip ts vs)
  where
    solveArg subst (t, v) = do
      newSubst <- (t @@ subst) `solve` v
      return $ subst .*. newSubst
a@(App _ _) `solve` v@(Var _) = fail $ show a ++ " `solve` " ++ show v
Var s `solve` t = return [(s, t)]
