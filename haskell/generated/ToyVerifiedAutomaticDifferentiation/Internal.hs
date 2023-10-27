module ToyVerifiedAutomaticDifferentiation.Internal where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

data Prod a b =
   Pair a b

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
proj1_sig :: a1 -> a1
proj1_sig e =
  e

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Sumor a =
   Inleft a
 | Inright

pred :: Nat -> Nat
pred n =
  case n of {
   O -> n;
   S u -> u}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

mul :: Nat -> Nat -> Nat
mul n m =
  case n of {
   O -> O;
   S p -> add m (mul p m)}

add0 :: Nat -> Nat -> Nat
add0 n m =
  case n of {
   O -> m;
   S p -> S (add0 p m)}

mul0 :: Nat -> Nat -> Nat
mul0 n m =
  case n of {
   O -> O;
   S p -> add0 m (mul0 p m)}

pow :: Nat -> Nat -> Nat
pow n m =
  case m of {
   O -> S O;
   S m0 -> mul0 n (pow n m0)}

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x) (succ p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
    (\_ -> (\x -> 2 Prelude.* x) 1)
    x

add1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add1 x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add1 p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add1 p q))
      (\q -> (\x -> 2 Prelude.* x) (add1 p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) q)
      (\_ -> (\x -> 2 Prelude.* x) 1)
      y)
    x

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x) (add_carry p q))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (add1 p q))
      (\_ -> (\x -> 2 Prelude.* x) (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> 2 Prelude.* x Prelude.+ 1) (succ q))
      (\q -> (\x -> 2 Prelude.* x) (succ q))
      (\_ -> (\x -> 2 Prelude.* x Prelude.+ 1) 1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x) p))
    (\p -> (\x -> 2 Prelude.* x Prelude.+ 1) (pred_double p))
    (\_ -> 1)
    x

data Mask =
   IsNul
 | IsPos Prelude.Integer
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos ((\x -> 2 Prelude.* x Prelude.+ 1) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos ((\x -> 2 Prelude.* x) p);
   x0 -> x0}

double_pred_mask :: Prelude.Integer -> Mask
double_pred_mask x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> IsPos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) p)))
    (\p -> IsPos ((\x -> 2 Prelude.* x) (pred_double p)))
    (\_ -> IsNul)
    x

sub_mask :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double_mask (sub_mask p q))
      (\q -> succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((\x -> 2 Prelude.* x) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\q -> double_mask (sub_mask p q))
      (\_ -> IsPos (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> IsNeg)
      (\_ -> IsNeg)
      (\_ -> IsNul)
      y)
    x

sub_mask_carry :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask_carry x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\q -> double_mask (sub_mask p q))
      (\_ -> IsPos (pred_double p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double_mask (sub_mask_carry p q))
      (\q -> succ_double_mask (sub_mask_carry p q))
      (\_ -> double_pred_mask p)
      y)
    (\_ -> IsNeg)
    x

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> 1}

mul1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul1 x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> add1 y ((\x -> 2 Prelude.* x) (mul1 p y)))
    (\p -> (\x -> 2 Prelude.* x) (mul1 p y))
    (\_ -> y)
    x

size_nat :: Prelude.Integer -> Nat
size_nat p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> S (size_nat p0))
    (\p0 -> S (size_nat p0))
    (\_ -> S O)
    p

compare_cont :: Comparison -> Prelude.Integer -> Prelude.Integer ->
                Comparison
compare_cont r x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont r p q)
      (\q -> compare_cont Gt p q)
      (\_ -> Gt)
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> compare_cont Lt p q)
      (\q -> compare_cont r p q)
      (\_ -> Gt)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\_ -> Lt)
      (\_ -> Lt)
      (\_ -> r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare =
  compare_cont Eq

ggcdn :: Nat -> Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
         (Prod Prelude.Integer Prelude.Integer)
ggcdn n a b =
  case n of {
   O -> Pair 1 (Pair a b);
   S n0 ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\a' ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\b' ->
        case compare a' b' of {
         Eq -> Pair a (Pair 1 1);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           Pair g p ->
            case p of {
             Pair ba aa -> Pair g (Pair aa
              (add1 aa ((\x -> 2 Prelude.* x) ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           Pair g p ->
            case p of {
             Pair ab bb -> Pair g (Pair (add1 bb ((\x -> 2 Prelude.* x) ab))
              bb)}}})
        (\b0 ->
        case ggcdn n0 a b0 of {
         Pair g p ->
          case p of {
           Pair aa bb -> Pair g (Pair aa ((\x -> 2 Prelude.* x) bb))}})
        (\_ -> Pair 1 (Pair a 1))
        b)
      (\a0 ->
      (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
        (\_ ->
        case ggcdn n0 a0 b of {
         Pair g p ->
          case p of {
           Pair aa bb -> Pair g (Pair ((\x -> 2 Prelude.* x) aa) bb)}})
        (\b0 ->
        case ggcdn n0 a0 b0 of {
         Pair g p -> Pair ((\x -> 2 Prelude.* x) g) p})
        (\_ -> Pair 1 (Pair a 1))
        b)
      (\_ -> Pair 1 (Pair 1 b))
      a}

ggcd :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
        (Prod Prelude.Integer Prelude.Integer)
ggcd a b =
  ggcdn (add (size_nat a) (size_nat b)) a b

iter_op :: (a1 -> a1 -> a1) -> Prelude.Integer -> a1 -> a1
iter_op op p a =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> op a (iter_op op p0 (op a a)))
    (\p0 -> iter_op op p0 (op a a))
    (\_ -> a)
    p

to_nat :: Prelude.Integer -> Nat
to_nat x =
  iter_op add x (S O)

of_nat :: Nat -> Prelude.Integer
of_nat n =
  case n of {
   O -> 1;
   S x -> case x of {
           O -> 1;
           S _ -> succ (of_nat x)}}

of_succ_nat :: Nat -> Prelude.Integer
of_succ_nat n =
  case n of {
   O -> 1;
   S x -> succ (of_succ_nat x)}

double :: Prelude.Integer -> Prelude.Integer
double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x) p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x) p))
    x

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x) 1)
    (\p -> (\x -> x) ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    (\p -> Prelude.negate (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate 1)
    (\p -> (\x -> x) (pred_double p))
    (\p -> Prelude.negate ((\x -> 2 Prelude.* x Prelude.+ 1) p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> double (pos_sub p q))
      (\q -> succ_double (pos_sub p q))
      (\_ -> (\x -> x) ((\x -> 2 Prelude.* x) p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> pred_double0 (pos_sub p q))
      (\q -> double (pos_sub p q))
      (\_ -> (\x -> x) (pred_double p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> Prelude.negate ((\x -> 2 Prelude.* x) q))
      (\q -> Prelude.negate (pred_double q))
      (\_ -> 0)
      y)
    x

opp :: Prelude.Integer -> Prelude.Integer
opp x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\x0 -> Prelude.negate x0)
    (\x0 -> (\x -> x) x0)
    x

compare0 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare0 x y =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Eq)
      (\_ -> Lt)
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Gt)
      (\y' -> compare x' y')
      (\_ -> Gt)
      y)
    (\x' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Lt)
      (\_ -> Lt)
      (\y' -> compOpp (compare x' y'))
      y)
    x

sgn :: Prelude.Integer -> Prelude.Integer
sgn z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\_ -> (\x -> x) 1)
    (\_ -> Prelude.negate 1)
    z

abs :: Prelude.Integer -> Prelude.Integer
abs z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> (\x -> x) p)
    (\p -> (\x -> x) p)
    z

to_nat0 :: Prelude.Integer -> Nat
to_nat0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> O)
    (\p -> to_nat p)
    (\_ -> O)
    z

of_nat0 :: Nat -> Prelude.Integer
of_nat0 n =
  case n of {
   O -> 0;
   S n0 -> (\x -> x) (of_succ_nat n0)}

to_pos :: Prelude.Integer -> Prelude.Integer
to_pos z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 1)
    (\p -> p)
    (\_ -> 1)
    z

ggcd0 :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
         (Prod Prelude.Integer Prelude.Integer)
ggcd0 a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Pair (abs b) (Pair 0 (sgn b)))
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Pair (abs a) (Pair (sgn a) 0))
      (\b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair ((\x -> x) g) (Pair ((\x -> x) aa) ((\x -> x)
          bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair ((\x -> x) g) (Pair ((\x -> x) aa)
          (Prelude.negate bb))}})
      b)
    (\a0 ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Pair (abs a) (Pair (sgn a) 0))
      (\b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair ((\x -> x) g) (Pair (Prelude.negate aa)
          ((\x -> x) bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair ((\x -> x) g) (Pair (Prelude.negate aa)
          (Prelude.negate bb))}})
      b)
    a

z_lt_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_lt_dec x y =
  case compare0 x y of {
   Lt -> Left;
   _ -> Right}

z_lt_ge_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_lt_ge_dec =
  z_lt_dec

z_lt_le_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
z_lt_le_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_lt_ge_dec x y)

pow_pos :: (a1 -> a1 -> a1) -> a1 -> Prelude.Integer -> a1
pow_pos rmul x i =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\i0 -> let {p = pow_pos rmul x i0} in rmul x (rmul p p))
    (\i0 -> let {p = pow_pos rmul x i0} in rmul p p)
    (\_ -> x)
    i

data Q =
   Qmake Prelude.Integer Prelude.Integer

qnum :: Q -> Prelude.Integer
qnum q =
  case q of {
   Qmake qnum0 _ -> qnum0}

qden :: Q -> Prelude.Integer
qden q =
  case q of {
   Qmake _ qden0 -> qden0}

qplus :: Q -> Q -> Q
qplus x y =
  Qmake
    ((Prelude.+) ((Prelude.*) (qnum x) ((\x -> x) (qden y)))
      ((Prelude.*) (qnum y) ((\x -> x) (qden x)))) (mul1 (qden x) (qden y))

qmult :: Q -> Q -> Q
qmult x y =
  Qmake ((Prelude.*) (qnum x) (qnum y)) (mul1 (qden x) (qden y))

qopp :: Q -> Q
qopp x =
  Qmake (opp (qnum x)) (qden x)

qminus :: Q -> Q -> Q
qminus x y =
  qplus x (qopp y)

qinv :: Q -> Q
qinv x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Qmake 0 1)
    (\p -> Qmake ((\x -> x) (qden x)) p)
    (\p -> Qmake (Prelude.negate (qden x)) p)
    (qnum x)

qlt_le_dec :: Q -> Q -> Sumbool
qlt_le_dec x y =
  z_lt_le_dec ((Prelude.*) (qnum x) ((\x -> x) (qden y)))
    ((Prelude.*) (qnum y) ((\x -> x) (qden x)))

qarchimedean :: Q -> Prelude.Integer
qarchimedean q =
  case q of {
   Qmake qnum0 _ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> 1)
      (\p -> add1 p 1)
      (\_ -> 1)
      qnum0}

qpower_positive :: Q -> Prelude.Integer -> Q
qpower_positive =
  pow_pos qmult

qpower :: Q -> Prelude.Integer -> Q
qpower q z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Qmake ((\x -> x) 1) 1)
    (\p -> qpower_positive q p)
    (\p -> qinv (qpower_positive q p))
    z

qabs :: Q -> Q
qabs x =
  case x of {
   Qmake n d -> Qmake (abs n) d}

pos_log2floor_plus1 :: Prelude.Integer -> Prelude.Integer
pos_log2floor_plus1 p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p' -> succ (pos_log2floor_plus1 p'))
    (\p' -> succ (pos_log2floor_plus1 p'))
    (\_ -> 1)
    p

qbound_lt_ZExp2 :: Q -> Prelude.Integer
qbound_lt_ZExp2 q =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x Prelude.+ 1) ((\x -> 2 Prelude.* x Prelude.+ 1)
    ((\x -> 2 Prelude.* x Prelude.+ 1) 1))))))))))
    (\p ->
    pos_sub (succ (pos_log2floor_plus1 p)) (pos_log2floor_plus1 (qden q)))
    (\_ -> 0)
    (qnum q)

data CReal =
   MkCReal (Prelude.Integer -> Q) Prelude.Integer

seq :: CReal -> Prelude.Integer -> Q
seq c =
  case c of {
   MkCReal seq0 _ -> seq0}

sig_forall_dec :: (Nat -> Sumbool) -> Sumor Nat
sig_forall_dec =
  Prelude.error "AXIOM TO BE REALIZED"

lowerCutBelow :: (Q -> Bool) -> Q
lowerCutBelow f =
  let {
   s = sig_forall_dec (\n ->
         let {b = f (qopp (Qmake (of_nat0 n) 1))} in
         case b of {
          True -> Right;
          False -> Left})}
  in
  case s of {
   Inleft a -> qopp (Qmake (of_nat0 a) 1);
   Inright -> false_rec}

lowerCutAbove :: (Q -> Bool) -> Q
lowerCutAbove f =
  let {
   s = sig_forall_dec (\n ->
         let {b = f (Qmake (of_nat0 n) 1)} in
         case b of {
          True -> Left;
          False -> Right})}
  in
  case s of {
   Inleft a -> Qmake (of_nat0 a) 1;
   Inright -> false_rec}

type DReal = (Q -> Bool)

dRealQlim_rec :: (Q -> Bool) -> Nat -> Nat -> Q
dRealQlim_rec f n p =
  case p of {
   O -> false_rec;
   S n0 ->
    let {
     b = f
           (qplus (proj1_sig (lowerCutBelow f)) (Qmake (of_nat0 n0)
             (of_nat (S n))))}
    in
    case b of {
     True ->
      qplus (proj1_sig (lowerCutBelow f)) (Qmake (of_nat0 n0) (of_nat (S n)));
     False -> dRealQlim_rec f n n0}}

dRealAbstr :: CReal -> DReal
dRealAbstr x =
  let {
   h = \q n ->
    let {
     s = qlt_le_dec
           (qplus q
             (qpower (Qmake ((\x -> x) ((\x -> 2 Prelude.* x) 1)) 1)
               (opp (of_nat0 n)))) (seq x (opp (of_nat0 n)))}
    in
    case s of {
     Left -> Right;
     Right -> Left}}
  in
  (\q -> case sig_forall_dec (h q) of {
          Inleft _ -> True;
          Inright -> False})

dRealQlim :: DReal -> Nat -> Q
dRealQlim x n =
  let {s = lowerCutAbove x} in
  let {s0 = qarchimedean (qminus s (proj1_sig (lowerCutBelow x)))} in
  dRealQlim_rec x n (mul (S n) (to_nat s0))

dRealQlimExp2 :: DReal -> Nat -> Q
dRealQlimExp2 x n =
  dRealQlim x (pred (pow (S (S O)) n))

cReal_of_DReal_seq :: DReal -> Prelude.Integer -> Q
cReal_of_DReal_seq x n =
  proj1_sig (dRealQlimExp2 x (to_nat0 (opp n)))

cReal_of_DReal_scale :: DReal -> Prelude.Integer
cReal_of_DReal_scale x =
  qbound_lt_ZExp2
    (qplus (qabs (cReal_of_DReal_seq x (Prelude.negate 1))) (Qmake ((\x -> x)
      ((\x -> 2 Prelude.* x) 1)) 1))

dRealRepr :: DReal -> CReal
dRealRepr x =
  MkCReal (cReal_of_DReal_seq x) (cReal_of_DReal_scale x)

type R = Prelude.Double

rabst :: CReal -> DReal
rabst =
  dRealAbstr

rrepr :: DReal -> CReal
rrepr =
  dRealRepr

rquot1 :: ()
rquot1 =
  __

rquot2 :: ()
rquot2 =
  __

type Rlt = ()

r0_def :: ()
r0_def =
  __

r1_def :: ()
r1_def =
  __

rplus_def :: ()
rplus_def =
  __

rmult_def :: ()
rmult_def =
  __

ropp_def :: ()
ropp_def =
  __

rlt_def :: ()
rlt_def =
  __

data Dual_num =
   Mk_dual R R

dual_value :: Dual_num -> R
dual_value x =
  case x of {
   Mk_dual r _ -> r}

dual_deriv :: Dual_num -> R
dual_deriv x =
  case x of {
   Mk_dual _ r -> r}

add_dual :: Dual_num -> Dual_num -> Dual_num
add_dual x y =
  Mk_dual (( Prelude.+ ) (dual_value x) (dual_value y))
    (( Prelude.+ ) (dual_deriv x) (dual_deriv y))

abs_dual :: Dual_num -> Dual_num
abs_dual x =
  Mk_dual (Prelude.abs (dual_value x)) (Prelude.signum (dual_value x))

eval_derivative :: (Dual_num -> Dual_num) -> R -> R
eval_derivative f x =
  dual_deriv (f (Mk_dual x (Prelude.fromIntegral ((\x -> x) 1))))

