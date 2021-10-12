module Main (main) where

import Control.Monad (void)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State.Strict (MonadState (..), State, StateT, evalStateT, runState)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Overeasy.EGraph (EGraph, egNew)
import Overeasy.UnionFind (MergeRes (..), UnionFind (..), ufAdd, ufMembers, ufMerge, ufNew, ufRoots, ufTotalSize)
import Test.Overeasy.Example (ArithF)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

applyS :: State s a -> StateT s IO a
applyS = state . runState

applyS_ :: State s a -> StateT s IO ()
applyS_ = void . applyS

testS :: (s -> IO a) -> StateT s IO a
testS p = get >>= liftIO . p

applyTestS :: State s a -> (a -> s -> IO b) -> StateT s IO b
applyTestS act check = do
  a <- applyS act
  s <- get
  liftIO (check a s)

runS :: s -> StateT s IO () -> IO ()
runS = flip evalStateT

type UF = UnionFind Char

runUF :: StateT UF IO () -> IO ()
runUF = runS ufNew

testUfSimple :: TestTree
testUfSimple = testCase "UF simple" $ runUF $ do
  testS $ \uf -> ufSize uf @?= 0
  testS $ \uf -> ufTotalSize uf @?= 0
  applyTestS ufRoots $ \rs _ -> rs @?= HashSet.empty
  applyS (ufAdd 'a')
  testS $ \uf -> ufSize uf @?= 1
  testS $ \uf -> ufTotalSize uf @?= 1
  applyTestS ufRoots $ \rs _ -> rs @?= HashSet.singleton 'a'
  applyS (ufAdd 'b')
  applyS (ufAdd 'c')
  testS $ \uf -> ufSize uf @?= 3
  testS $ \uf -> ufTotalSize uf @?= 3
  applyTestS ufRoots $ \rs _ -> rs @?= HashSet.fromList "abc"
  applyTestS (ufMerge 'a' 'c') $ \res uf -> do
    res @?= MergeResChanged 'a' 'c' 'a'
    ufSize uf @?= 2
    ufTotalSize uf @?= 3
  applyTestS ufRoots $ \rs _ -> rs @?= HashSet.fromList "ab"
  applyTestS ufMembers $ \rs _ -> rs @?= HashMap.fromList [('a', HashSet.fromList "ac"), ('b', HashSet.fromList "b")]
  applyTestS (ufMerge 'c' 'a') $ \res _ -> res @?= MergeResUnchanged 'a'
  applyTestS (ufMerge 'b' 'z') $ \res _ -> res @?= MergeResMissing 'z'

testUfRec :: TestTree
testUfRec = testCase "UF rec" $ runUF $ do
  applyS (ufAdd 'a')
  applyS (ufAdd 'b')
  applyS (ufAdd 'c')
  applyS_ (ufMerge 'b' 'c')
  applyS_ (ufMerge 'a' 'c')
  testS $ \uf -> do
    ufSize uf @?= 1
    ufTotalSize uf @?= 3
  applyTestS ufRoots $ \rs _ -> rs @?= HashSet.fromList "a"
  applyTestS ufMembers $ \rs _ -> rs @?= HashMap.fromList [('a', HashSet.fromList "abc")]

testUf :: TestTree
testUf = testGroup "UF" [testUfSimple, testUfRec]

type EG = EGraph () ArithF

runEG :: StateT EG IO () -> IO ()
runEG = runS egNew

testEgSimple :: TestTree
testEgSimple = testCase "EG simple" $ runEG $ do
  pure ()

testEg :: TestTree
testEg = testGroup "EG" [testEgSimple]

main :: IO ()
main = defaultMain (testGroup "Overeasy" [testUf , testEg])
