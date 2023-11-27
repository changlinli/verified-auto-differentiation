# Verified (Toy) Automatic Differentiation

This is a Coq project that aims to provide a verified implementation of
single-variable automatic differentiation. This happens to be something that is
fairly straightforward, but is just a notch more complex than something like
e.g. `leftpad` (see e.g.
[https://github.com/hwayne/lets-prove-leftpad](https://github.com/hwayne/lets-prove-leftpad)).

The Coq code here is extracted to form a Haskell library which is contained
under the `haskell` directory.

*This is not meant to be used in production!* Apart from only demonstrating
automatic differentiation in a single variable (which is usually not enough for
real-world use cases), the extraction process of Coq to runnable Haskell code is
finicky enough that any correctness guarantees proved in the Coq code may be
severely compromised in the final Haskell code. In particular:

1. I extract the Coq code to floating point arithmetic in Haskell whereas the
   Coq proofs are carried out with Coq's axiomatic real numbers. Floating point
   behavior can deviate significantly from real number behavior in certain
   circumstances.
2. Coq's axiomatic real numbers are not computable. Hence in the extraction to
   Haskell code I take certain short cuts to preserve computability. I do not
   prove that these short cuts do not compromise the proof!

In general these two things are pretty difficult to get around in Coq. Proving
things directly using either floating point numbers or computable real numbers,
makes the resulting Coq proof *much* more difficult and many definitions must be
restated from scratch.

This means that in general Coq formal verification of properties about the real
numbers are a bit suspect when extracted to some other target language. They
provide at least some confidence that we've gotten things right, but not as
airtight a guarantee as in other cases.

## Overall Approach

The main interesting part of writing this code was coming up with the proper
definition for what it meant for an auto-differentiation system to be correct.

This code provides two theorems that correspond to a naive definition and a
slightly more sophisticated definition.

The naive definition of correctness is the following:

```coq
Theorem auto_differentiate_is_correct :
  forall f : dual_num -> dual_num, is_well_formed f -> derivative_is_correct f.
```

We first require some sort of well-formedness condition on the `f` in question.
This is because any auto-differentiation library can have its correctness
compromised by a user writing from scratch their own functions on the dual
numbers that have the incorrect derivative. Generally an auto-differentiation
library only preserves correctness if all functions used are built with the
library's provided functions and no other.

The `is_well_formed` condition is one way of stating this condition, which
states that there is an AST constructed using only the functions provided by the
auto-differentiation library that corresponds to the `f` in question.

```coq
Definition is_well_formed (f : dual_num -> dual_num) : Prop :=
  exists ast : auto_diff_ast, eval_ast_dual ast = f.
```

The definition `derivative_is_correct` then says that the derivative calculated
by the auto-differentiation mechanism agrees with the actual theoretical
derivative (`derivative_at_point_is`).

```coq
Definition derivative_is_correct (f_dual : dual_num -> dual_num) : Prop :=
  let f := eval_value f_dual in
  let f' := eval_derivative f_dual in
  forall x : R, derivative_at_point_is f x (f' x).
```

This is naive because this theorem only works for auto-differentiation libraries
that consist of everywhere-differentiable functions. But many
auto-differentiation libraries include examples of functions which are not
differentiable everywhere, such as the absolute value function, which is not
differentiable at `0`.

In that case our theorem breaks down because most auto-differentiation libraries
will continue to give an answer even if the theoretical derivative doesn't exist
there. Hence, our auto-differentiation library will not always agree with the
theoretical derivative.

Perhaps the most obvious way of dealing with this does not work, namely simply
loosing our condition to say that *if the theoretical derivative exists* then
our auto-differentiation library agrees with the theoretical derivative.

This is because our well-formedness constraint is no longer strong enough, since
an everywhere-differentiable function can be formed from the composition of
functions which are not themselves everywhere-differentiable.

E.g. the mathematical function `f(x) = abs(x) - abs(x)` is equal to the
mathematical function `f(x) = 0`, but auto-differentiation libraries are
sensitive to differences between those two functions.

Hence instead of requiring that the theoretical derivative exists at a given
point, we instead require that the derivative as calculated by the
auto-differentiation library is actually a proper derivative at that point, and
keep track of which points are not differentiable among the base functions
distributed by the auto-differentiation library.

## Building and Executing

The included `build.sh` will verify the Coq code and extract the Haskell code to
the `haskell` folder. From the `haskell` folder, the usual invocation of `cabal
build` to build the project from within that folder should work.

The version of Coq used was `8.17.1`. The version of GHC used was `9.2.8`.
