Require Coq.extraction.Extraction.
Require Import Coq.extraction.ExtrHaskellZInteger.
Require Import Coq.extraction.ExtrHaskellNatInteger.
Require Import VerifiedAutoDiff.
Extraction Language Haskell.

(* Adapted from https://github.com/inQWIRE/SQIR/blob/a76b448bf2d922ec9f495ca3f599534d0437cda5/examples/ghz/extraction/ExtrOcamlR.v#L4 *)

Require Import Reals.
Require Import QArith.
Require Import Coq.Numbers.BinNums.

Extract Constant R => "Prelude.Double".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant Rplus => "( Prelude.+ )".
Extract Inlined Constant Rmult => "( Prelude.* )".
Extract Inlined Constant Ropp => "((Prelude.-) 0.0)".
Extract Inlined Constant Rinv => "((Prelude./) 1.0)".
Extract Inlined Constant Rminus => "( Prelude.- )".
Extract Inlined Constant Rdiv => "( Prelude./ )".
Extract Inlined Constant pow => "(\ a b -> a Prelude.^ b)".
Extract Inlined Constant cos => "Prelude.cos".
Extract Inlined Constant sin => "Prelude.sin".
Extract Inlined Constant tan => "Prelude.tan".
Extract Inlined Constant atan => "Prelude.atan".
Extract Inlined Constant acos => "Prelude.acos".
Extract Inlined Constant asin => "Prelude.asin".
Extract Inlined Constant sinh => "Prelude.asinh".
Extract Inlined Constant cosh => "Prelude.acosh".
Extract Inlined Constant tanh => "Prelude.tanh".
Extract Inlined Constant arcsinh => "Prelude.asinh".
Extract Inlined Constant arccosh => "Prelude.acosh".
Extract Inlined Constant arctanh => "Prelude.atanh".
Extract Inlined Constant PI => "Prelude.pi".
Extract Inlined Constant IZR => "Prelude.fromIntegral".
Extract Inlined Constant INR => "Prelude.fromIntegral".
Extract Inlined Constant Rsignum => "Prelude.signum".
Extract Inlined Constant Rabs => "Prelude.abs".
Extract Inlined Constant Q2R => "Prelude.fromRational".
Extract Inlined Constant Rsqrt => "Prelude.sqrt".
Extract Inlined Constant sqrt => "Prelude.sqrt".
Extract Inductive positive => "Prelude.Integer" ["(\x -> shiftL x 1 Prelude.+ 1)" "(\x -> shiftL x 1)" "1"].
Extract Inductive Q => "Prelude.Rational" ["(:%)"].

Open Scope R.

Extraction "haskell/generated/ToyVerifiedAutomaticDifferentiation/Internal.hs"
  add_dual
  multiply_dual
  subtract_dual
  negate_dual
  abs_dual
  signum_dual
  from_integer_dual
  eval_derivative
  eval_value
  from_rational_dual
  divide_dual
  recip_dual
  acosh_dual
  .
