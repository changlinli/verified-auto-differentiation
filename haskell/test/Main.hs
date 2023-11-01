module Main (main) where

import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Test.Tasty.Hedgehog as HH

import Data.Function ((&))
import Hedgehog ((===))
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import ToyVerifiedAutomaticDifferentiation

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
  , HH.testProperty "dummy property" $
      testComplicatedSetOfFunctionsHasNoRuntimeExceptions
  ]

dummyProperty :: Hedgehog.Property
dummyProperty =
    Hedgehog.property $ do
        x <- Hedgehog.forAll $ Gen.int (Range.linear 1 10)
        x === x

testComplicatedSetOfFunctionsHasNoRuntimeExceptions :: Hedgehog.Property
testComplicatedSetOfFunctionsHasNoRuntimeExceptions =
    let
        -- Let's use every operation possible
        num_f :: DualNum -> DualNum
        num_f x = (x + 1) * (x - 5) + abs x * negate x + signum x
        frac_f :: DualNum -> DualNum
        frac_f x = x / 5 + recip x
        float_f :: DualNum -> DualNum
        float_f x = pi * x + exp x + log x + sin x + cos x + tan x + asin x + acos x + atan x + sinh x + cosh x + tanh x + asinh x + acosh x + atanh x
        f :: DualNum -> DualNum
        f x = float_f . frac_f . num_f $ x
    in
    Hedgehog.property $ do
        x <- Hedgehog.forAll $ Gen.double (Range.linearFrac (-100) 100)
        let result = f $$ x
        -- This just a nice way to make sure that we don't have runtime
        -- exceptions
        if isNaN result 
           then Hedgehog.success
           else result === result


unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "dummy unit test" $
      1 @?= 1
  ]

main :: IO ()
main = defaultMain tests
