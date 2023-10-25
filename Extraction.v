Require Coq.extraction.Extraction.
Require Import VerifiedAutoDiff.
Extraction Language Haskell.

(* Adapted from https://github.com/inQWIRE/SQIR/blob/a76b448bf2d922ec9f495ca3f599534d0437cda5/examples/ghz/extraction/ExtrOcamlR.v#L4 *)

Require Import Reals.

Extract Constant R => "Prelude.Double".
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant Rplus => "( Prelude.+ )".
Extract Inlined Constant Rmult => "( Prelude.* )".
Extract Inlined Constant Ropp => "((Prelude.-) 0.0)".
Extract Inlined Constant Rinv => "((Prelude./) 1.0)".
Extract Inlined Constant Rminus => "( Prelude.- )".
Extract Inlined Constant Rdiv => "( Prelude./ )".
Extract Inlined Constant pow => "(\ a b -> a Prelude.** b)".
Extract Inlined Constant cos => "Prelude.cos".
Extract Inlined Constant sin => "Prelude.sin".
Extract Inlined Constant tan => "Prelude.tan".
Extract Inlined Constant atan => "Prelude.atan".
Extract Inlined Constant acos => "Prelude.acos".
Extract Inlined Constant PI => "Prelude.pi".
Extract Inlined Constant IZR => "Prelude.fromIntegral".
Extract Inlined Constant INR => "Prelude.fromIntegral".

Open Scope R.

Extraction "haskell/generated/ToyVerifiedAutomaticDifferentiation/Internal.hs" add_dual eval_derivative.
