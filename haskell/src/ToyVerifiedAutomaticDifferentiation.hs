{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module ToyVerifiedAutomaticDifferentiation
    ( DualNum
    , evalDerivative
    , evalValue
    , ($|)
    , ($$)
    , toy_example
    , toy_example_deriv
    )
    where

import qualified ToyVerifiedAutomaticDifferentiation.Internal as TI

instance Num TI.Dual_num where
    (+) = TI.add_dual
    (*) = TI.multiply_dual
    (-) = TI.subtract_dual
    negate = TI.negate_dual
    abs = TI.abs_dual
    signum = TI.signum_dual
    fromInteger = TI.from_integer_dual

instance Fractional TI.Dual_num where
    (/) = TI.divide_dual
    recip = TI.recip_dual
    fromRational = TI.from_rational_dual

instance Floating TI.Dual_num where
    pi = TI.pi_dual
    exp = TI.exp_dual
    log = TI.log_dual
    sin = TI.sin_dual
    cos = TI.cos_dual
    tan = TI.tan_dual
    asin = TI.asin_dual
    acos = TI.acos_dual
    atan = TI.atan_dual
    sinh = TI.sinh_dual
    cosh = TI.cosh_dual
    tanh = TI.tanh_dual
    asinh = TI.asinh_dual
    acosh = TI.acosh_dual
    atanh = TI.atanh_dual

newtype DualNum = DualNum { unDualNum :: TI.Dual_num }
    deriving newtype (Num, Fractional, Floating)

convertToF1 :: (DualNum -> DualNum) -> TI.Dual_num -> TI.Dual_num
convertToF1 f = \d -> unDualNum (f (DualNum d))

evalDerivative :: (DualNum -> DualNum) -> Double -> Double
evalDerivative f x = TI.eval_derivative (convertToF1 f) x

($|) :: (DualNum -> DualNum) -> Double -> Double
($|) = evalDerivative

evalValue :: (DualNum -> DualNum) -> Double -> Double
evalValue f x = TI.eval_value (convertToF1 f) x

($$) :: (DualNum -> DualNum) -> Double -> Double
($$) = evalValue

f :: DualNum -> DualNum
f x = x * x + 2 * x / x

toy_example :: Double
toy_example = f $$ 3

toy_example_deriv :: Double
toy_example_deriv = f $| 3
