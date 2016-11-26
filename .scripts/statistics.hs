module Statistics where

import System.Environment
import Text.ParserCombinators.Parsec
import Text.Parsec.String
import Data.Either
import Data.Maybe
import Text.Read
import Control.Monad
import Numeric
-- import Text.PrettyPrint

stats = garbage >> endBy stat garbage
stat = do
  string "BEGIN-STATS\n("
  s <- sepBy line newline
  string ")\nEND-STATS"
  return s
line = do
  spaces >> char ':'
  i <- ident
  spaces
  v <- value
  return (i,v)
ident = many (letter <|> char '-')
value = many (digit <|> char '.')
garbage = manyTill anyChar (eof <|> void (try (lookAhead (string "BEGIN-STATS"))))

parseStats :: String -> IO [[(String, String)]]
parseStats input = do
  s <- parseFromFile stats input
  case s of
    Left e -> error $ show e
    Right s -> return s

data Stat = Stat {rlimitCount :: Int,
                  time :: Float}

instance Show Stat where
  show st = show (rlimitCount st) ++ "  " ++ showFFloat (Just 2) (time st) ""

processStat' :: [(String, String)] -> Maybe Stat
processStat' m = do
  rc <- lookup "rlimit-count" m >>= readMaybe
  t  <- lookup "time" m >>= readMaybe
  return Stat {rlimitCount = rc, time = t}

processStat :: [(String, String)] -> IO Stat
processStat m =
  case processStat' m of
    Nothing -> error $ "Failed to process: " ++ show m
    Just m -> return m

processStats :: [[(String, String)]] -> IO [Stat]
processStats = mapM processStat

showStats :: [Stat] -> String
showStats s = unlines $ map show s

main :: IO ()
main = do
  args <- getArgs
  s <- parseStats (head args)
  s' <- processStats s
  putStr $ showStats s'
