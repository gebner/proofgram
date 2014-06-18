module Proofgram.CNF where

import Control.Lens
import Control.Applicative

import Proofgram.Syntax

data Literal = Pos Atom | Min Atom
             deriving (Eq, Show)

type Clause = [Literal]

makePrisms ''Literal

atom :: Traversal' Literal Atom
atom f (Pos a) = Pos <$> f a
atom f (Min a) = Min <$> f a

nnf :: Formula -> Formula
nnf (Neg (And a b)) = Or (nnf (Neg a)) (nnf (Neg b))
nnf (Neg (Or a b)) = And (nnf (Neg a)) (nnf (Neg b))
nnf (Neg (Neg a)) = nnf a
nnf (Neg T) = F
nnf (Neg F) = T

nnf l@(Atom _) = l
nnf l@(Neg (Atom _)) = l

nnf (And a b) = And (nnf a) (nnf b)
nnf (Or a b) = Or (nnf a) (nnf b)
nnf T = T
nnf F = F

formula2cnf :: Formula -> [Clause]
formula2cnf = formula2cnf' . nnf

formula2cnf' :: Formula -> [Clause]
formula2cnf' (And a b) = formula2cnf' a ++ formula2cnf' b
formula2cnf' (Or a b) = do
    c <- formula2cnf' a
    d <- formula2cnf' b
    return $ c ++ d
formula2cnf' (Neg (Atom a)) = [[Min a]]
formula2cnf' (Atom a) = [[Pos a]]
formula2cnf' F = [[]]
formula2cnf' T = []

formula2cnf' rest = error $ "formula2cnf' only defined for NNF formulae, not for " ++ show rest

cnf2formula :: [Clause] -> Formula
cnf2formula = foldl And T . map (foldl Or F . map lit2formula)

lit2formula :: Literal -> Formula
lit2formula (Pos a) = Atom a
lit2formula (Min a) = Neg (Atom a)

cnf :: Iso' Formula [Clause]
cnf = iso formula2cnf cnf2formula
