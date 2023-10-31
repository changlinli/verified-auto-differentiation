#!/usr/bin/env bash

coq_makefile -f _CoqProject -o Makefile
make
cat haskell/generated/ToyVerifiedAutomaticDifferentiation/Internal.hs | sed s/\ Internal/\ ToyVerifiedAutomaticDifferentiation\.Internal/ | sed s/"import qualified Prelude"/"import qualified Prelude\nimport Data.Bits\nimport GHC.Real"/ > tmpfile && mv tmpfile haskell/generated/ToyVerifiedAutomaticDifferentiation/Internal.hs
