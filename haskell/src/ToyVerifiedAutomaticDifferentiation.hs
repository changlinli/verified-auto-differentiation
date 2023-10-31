{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module ToyVerifiedAutomaticDifferentiation
    ( DualNum
    , evalDerivative
    , evalValue
    , ($|)
    , ($$)
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
    fromRational = TI.from_rational

newtype DualNum = DualNum { unDualNum :: TI.Dual_num }
    deriving newtype (Num)

convertFromF1 :: (TI.Dual_num -> TI.Dual_num) -> DualNum -> DualNum
convertFromF1 f = \(DualNum d) -> DualNum (f d)

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
