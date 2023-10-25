#!/usr/bin/env bash

coq_makefile -f _CoqProject -o Makefile
make
cat haskell/generated/ToyVerifiedAutomaticDifferentiation/Internal.hs | sed s/\ Internal/\ ToyVerifiedAutomaticDifferentiation\.Internal/ > tmpfile && mv tmpfile haskell/generated/ToyVerifiedAutomaticDifferentiation/Internal.hs
