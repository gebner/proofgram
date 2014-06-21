module Proofgram.Grammar where

import Control.Lens
import Data.List

import Proofgram.Syntax

data RatGrammar = RatGrammar { _axiom :: Symbol, _rules :: [(Symbol, Term)] }
                deriving (Eq,Ord,Show)

makeLenses ''RatGrammar

nonTerminals :: RatGrammar -> [Symbol]
nonTerminals g = nub $ sort $ g ^.. rules.traverse._1

orderedRules :: RatGrammar -> [Symbol]
orderedRules g
  | null (g ^. rules) = []
  | otherwise = nextNonTerminals ++ orderedRules (g & rules %~ filter ((`notElem` nextNonTerminals) . fst))
    where
      nextNonTerminals = nonTerminals g \\ rhsNonTerminals
      rhsNonTerminals = g ^.. rules.traverse._2.variables._Var

productions :: RatGrammar -> Symbol -> [Term]
productions g n = map snd $ filter ((== n) . fst) (g ^. rules)

normalForm :: RatGrammar -> RatGrammar
normalForm g = g & rules .~ [ (n, p) | n <- orderedRules g, p <- productions g n ]

allWords :: RatGrammar -> Term -> [Term]
allWords g  = allWords' (normalForm g)

allWords' :: RatGrammar -> Term -> [Term]
allWords' g t = case g ^? rules . taking 1 traverse . _1 of
    Just n -> do
      prod <- map snd $ filter ((== n) . fst) (g ^. rules)
      allWords (g & rules %~ filter ((/= n) . fst)) (t @@ [(n, prod)])
    Nothing -> return t

language :: RatGrammar -> [Term]
language g = allWords g (g ^. axiom . to Var)
