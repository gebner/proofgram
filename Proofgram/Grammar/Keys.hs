module Proofgram.Grammar.Keys where

import Control.Monad
import Data.List

import Proofgram.Syntax

allPossibleKeys :: [Symbol] -> [Term] -> [Term]
allPossibleKeys vars lang = do
    word <- lang
    allPossibleKeys' vars word

allPossibleKeys' :: [Symbol] -> Term -> [Term]
allPossibleKeys' vars word = do
    replacement <- word : map Var vars
    case replacement of
      Var _ -> return replacement
      App s ts -> App s `liftM` mapM (allPossibleKeys' vars) ts

allPossibleRHS :: [Symbol] -> [Term] -> [Term]
allPossibleRHS vars = nub.sort . allPossibleKeys vars . nub.sort . concatMap subTerms
