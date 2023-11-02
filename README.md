# Verified (Toy) Automatic Differentiation

This is a Coq project that aims to provide a verified implementation of
single-variable automatic differentiation. This happens to be something that is
fairly straightforward, but is just a notch more complex than something like
e.g. `leftpad` (see e.g.
[https://github.com/hwayne/lets-prove-leftpad](https://github.com/hwayne/lets-prove-leftpad)).

The Coq code here is extracted to form a Haskell library which is contained
under the `haskell` directory.
