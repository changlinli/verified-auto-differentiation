module Main (main) where

import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Test.Tasty.Hedgehog as HH

import Data.Function ((&))
import Hedgehog ((===))
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestTree
tests = testGroup "Tests"
  [ properties
  , unitTests
  ]

properties :: TestTree
properties = testGroup "Properties"
  [ hedgehogProperties
  ]

hedgehogProperties :: TestTree
hedgehogProperties = testGroup "(checked by Hedgehog)"
  [ HH.testProperty "dummy property" $
      dummyProperty
  ]

dummyProperty :: Hedgehog.Property
dummyProperty =
    Hedgehog.property $ do
        x <- Hedgehog.forAll $ Gen.int (Range.linear 1 10)
        x === x

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "dummy unit test" $
      1 @?= 1
  ]

main :: IO ()
main = defaultMain tests
