{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}

module Proofgram.Prover9 where

import Control.Lens
import Control.Applicative hiding ((<|>), many)
import Data.Maybe
import Data.List
import qualified Data.HashMap.Lazy as HM
import Text.Parsec hiding (labels)
import Text.Parsec.String
import System.Process
import System.Exit

import Proofgram.Syntax
import Proofgram.CNF

data P9Clause = P9Clause { _p9clauseClause :: Clause, _p9clauseLabels :: [String] }
              deriving (Eq, Show)

type ClauseNum = String

type LitNum = Int

p9LitNum :: Iso' LitNum String
p9LitNum = iso litNum2p9litNum p9litNum2litNum
  where
    litNum2p9litNum i = [toEnum (i + fromEnum 'a')]
    p9litNum2litNum [c] = fromEnum c - fromEnum 'a'
    p9litNum2litNum _ = undefined

type P9TermPath = [Int]

p9TermAt :: Path -> Traversal' Literal Term
p9TermAt (predArgNum : termPath) = atom . elementOf predicateArguments (predArgNum-1) . subTermAt (map pred termPath)

data PrimaryStep
    = Assumption
    | Resolve ClauseNum LitNum ClauseNum LitNum
    | Para ClauseNum LitNum Path ClauseNum LitNum Path
    | Copy ClauseNum
    deriving (Eq, Show)

data SecondaryStep
    = Flip LitNum
    | XX LitNum
    deriving (Eq, Show)

data ProofStep = ProofStep { _pstepStepNum :: String
                           , _pstepClause :: P9Clause
                           , _pstepJ1 :: PrimaryStep
                           , _pstepJ2 :: Maybe SecondaryStep
                           }
               deriving (Eq, Show)

type Proof = [ProofStep]

makeFields ''P9Clause
makePrisms ''PrimaryStep
makePrisms ''SecondaryStep
makeFields ''ProofStep

tok s = string s >> spaces >> return ()

ident :: Parser String
ident = many1 (alphaNum <|> oneOf "_") <* spaces

parseTerm = do
    sym <- ident
    args <- tok "(" *> sepBy parseTerm (tok ",") <* tok ")" <|> return []
    let isVariable = head sym `elem` ['u'..'z']
    return $ if isVariable then Var sym else App sym args

parsePred = do
    sym <- ident
    args <- tok "(" *> sepBy parseTerm (tok ",") <* tok ")" <|> return []
    return $ Pred sym args

parseMinPred = Min <$> (tok "-" *> parsePred)
parsePosPred = Pos <$> parsePred

parseEq = Pos <$> (Eq <$> parseTerm <* tok "=" <*> parseTerm)
parseNeq = Min <$> (Eq <$> parseTerm <* tok "!=" <*> parseTerm)

parseLiteral = parseMinPred <|> try parseEq <|> try parseNeq <|> parsePosPred

parseClause = do
    lits <- try (tok "$F" *> return []) <|> parseLiteral `sepBy` tok "|"
    labls <- many $ try $ tok "# label(" *> ident <* tok ")"
    answers <- many $ tok "# answer(" *> ident <* tok ")"
    _ <- tok "."
    return $ P9Clause lits labls

number = read <$> many1 digit

parseClauseNum = ident
parseLitNum = (^. from p9LitNum) <$> ident
parsePath = number `sepBy` char ','

parseAssumption = string "assumption" *> pure Assumption
parseResolve =
    Resolve <$> (string "resolve(" *> parseClauseNum <* char ',')
            <*> (parseLitNum <* char ',')
            <*> (parseClauseNum <* char ',')
            <*> (parseLitNum <* char ')')
parsePara =
    Para <$> (string "para(" *> parseClauseNum <* char '(')
            <*> (parseLitNum <* char ',')
            <*> (parsePath <* char ')')
            <*> (char ',' *> parseClauseNum <* char '(')
            <*> (parseLitNum <* char ',')
            <*> (parsePath <* string "))")
parseCopy = Copy <$> (string "copy(" *> parseClauseNum <* char ')')

parsePrimaryJustification =
    try parseAssumption <|> try parseResolve <|> try parsePara <|> parseCopy

parseFlip = Flip <$> (string "flip(" *> parseLitNum <* char ')')
parseXX = XX <$> (string "xx(" *> parseLitNum <* char ')')

parseSecondaryJustification = parseFlip <|> parseXX

parseProofStep = do
    num <- parseClauseNum
    cls <- parseClause
    tok "["
    j1 <- parsePrimaryJustification
    j2 <- try (Just <$> (char ',' *> parseSecondaryJustification)) <|> return Nothing
    tok "]."
    return $ ProofStep num cls j1 j2

renaming i clause = [ (n, Var $ n ++ "_" ++ i) | n <- clause ^.. traverse . atom . predicateArguments . variables . _Var ]

paramodulate :: Clause -> LitNum -> P9TermPath -> Clause -> LitNum -> P9TermPath -> Maybe (Subst, Subst, Clause)
paramodulate c1 l1 p1 c2 l2 p2 = do
  let s1 = renaming "t1" c1
  let s2 = renaming "t2" c2
  let c1' = c1 & traverse . atom . predicateArguments %~ (@@ s1)
  let c2' = c2 & traverse . atom . predicateArguments %~ (@@ s2)
  t1' <- c1' ^? ix l1 . p9TermAt p1
  t2' <- c2' ^? ix l2 . p9TermAt p2
  unif <- t1' `mgu` t2'
  t1replacement' <- c1' ^? ix l1 . p9TermAt [2]
  let pm = [ l | (i, l) <- zip [0..] c1', i /= l1 ] ++ (c2' & ix l2 . p9TermAt p2 %~ const t1replacement')
  return $ (s1 .*. unif, s2 .*. unif, pm & traverse . atom . predicateArguments %~ (@@ unif))

resolve :: Clause -> LitNum -> Clause -> LitNum -> Maybe (Subst, Subst, Clause)
resolve c1 l1 c2 l2 = do
  let s1 = renaming "t1" c1
  let s2 = renaming "t2" c2
  let c1' = c1 & traverse . atom . predicateArguments %~ (@@ s1)
  let c2' = c2 & traverse . atom . predicateArguments %~ (@@ s2)
  let t1' = c1' ^.. ix l1 . atom . predicateArguments
  let t2' = c2' ^.. ix l2 . atom . predicateArguments
  unif <- App [] t1' `mgu` App [] t2'
  let res = [ l | (i, l) <- zip [0..] c1', i /= l1 ] ++ [ l | (i, l) <- zip [0..] c2', i /= l2 ]
  return $ (s1 .*. unif, s2 .*. unif, res & traverse . atom . predicateArguments %~ (@@ unif))

hseqForStep :: HM.HashMap ClauseNum ProofStep -> ProofStep -> HM.HashMap ClauseNum [Term] -> [Term]
hseqForStep proof step hseqs =
    case step ^. j1 of
      Assumption -> [App (step ^. clause . labels . traverse) (nub . sort $ step ^.. clause . clause . traverse . atom . predicateArguments . variables)]
      Copy clauseNum -> hseqs ^. ix clauseNum
      Para c1 l1 p1 c2 l2 p2 -> fromJust $ do
        cl1 <- proof ^? ix c1 . clause . clause
        cl2 <- proof ^? ix c2 . clause . clause
        (s1, s2, paramodulant) <- paramodulate cl1 l1 p1 cl2 l2 p2
        let pmTerms = paramodulant ^.. traverse . atom . predicateArguments
        let p9Terms = step ^.. clause . clause . traverse . atom . predicateArguments
        let backsubst = zip pmTerms p9Terms ^.. traverse . to (uncurry solve) . _Just . traverse
        return $ (hseqs ^.. ix c1 . traverse . to (@@ (s1 .*. backsubst))) ++ (hseqs ^.. ix c2 . traverse . to (@@ (s2 .*. backsubst)))
      Resolve c1 l1 c2 l2 -> fromJust $ do
        cl1 <- proof ^? ix c1 . clause . clause
        cl2 <- proof ^? ix c2 . clause . clause
        (s1, s2, res) <- resolve cl1 l1 cl2 l2
        let resTerms = res ^.. traverse . atom . predicateArguments
        let p9Terms = step ^.. clause . clause . traverse . atom . predicateArguments
        let backsubst = zip resTerms p9Terms ^.. traverse . to (uncurry solve) . _Just . traverse
        return $ (hseqs ^.. ix c1 . traverse . to (@@ (s1 .*. backsubst))) ++ (hseqs ^.. ix c2 . traverse . to (@@ (s2 .*. backsubst)))

proofMap proof = HM.fromList [ (s ^. stepNum, s) | s <- proof ]

hseqsForProof :: Proof -> HM.HashMap ClauseNum [Term]
hseqsForProof proof = hseqs
    where
      hseqs = HM.fromList [ (s ^. stepNum, hseqForStep (proofMap proof) s hseqs) | s <- proof ]

hseqForProof :: Proof -> [Term]
hseqForProof proof = fromJust $ hseqsForProof proof ^. at (last proof ^. stepNum)

parseProver9Output :: String -> Proof
parseProver9Output output = lines output ^.. traverse . to parseLine . _Right
  where parseLine = runParser parseProofStep () ""

writeTerm (App s []) = s
writeTerm (App s ts) = s ++ "(" ++ intercalate "," (map writeTerm ts) ++ ")"
writeTerm (Var s) = s

writeLiteral (Min (Eq a b)) = show a ++ " != " ++ show b
writeLiteral (Pos (Eq a b)) = show a ++ " = " ++ show b
writeLiteral (Min (Pred t ts)) = "-" ++ writeTerm (App t ts)
writeLiteral (Pos (Pred t ts)) = writeTerm (App t ts)

writeClause lits = intercalate " | " (map writeLiteral lits)

writeP9Clause c = writeClause (c ^. clause) ++ concatMap (\l -> " # label(" ++ l ++ ")") (c ^. labels) ++ "."

writeSOS cs = unlines $ ["formulas(sos)."] ++ map writeP9Clause cs ++ ["end_of_list."]

runProver9 :: [P9Clause] -> IO (Maybe Proof)
runProver9 cs = do
    (exitCode, stdout, stderr) <- readProcessWithExitCode "sh" ["-c", "prover9 | prooftrans expand"] (writeSOS cs)
    case exitCode of
      ExitFailure _ -> do
        putStrLn stderr
        putStrLn stdout
        return Nothing
      ExitSuccess -> return $ Just $ parseProver9Output stdout
