module ToyVerifiedAutomaticDifferentiation.Internal where

import qualified Prelude
import Data.Bits
import GHC.Real

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

pred :: Prelude.Integer -> Prelude.Integer
pred = (\n -> Prelude.max 0 (Prelude.pred n))

pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Prelude.succ 0)
    (\m0 -> (Prelude.*) n (pow n m0))
    m

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> shiftL x 1) (succ p))
    (\p -> (\x -> shiftL x 1 Prelude.+ 1) p)
    (\_ -> (\x -> shiftL x 1) 1)
    x

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> shiftL x 1) (add_carry p q))
      (\q -> (\x -> shiftL x 1 Prelude.+ 1) (add p q))
      (\_ -> (\x -> shiftL x 1) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> shiftL x 1 Prelude.+ 1) (add p q))
      (\q -> (\x -> shiftL x 1) (add p q))
      (\_ -> (\x -> shiftL x 1 Prelude.+ 1) p)
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> shiftL x 1) (succ q))
      (\q -> (\x -> shiftL x 1 Prelude.+ 1) q)
      (\_ -> (\x -> shiftL x 1) 1)
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
      (\q -> (\x -> shiftL x 1 Prelude.+ 1) (add_carry p q))
      (\q -> (\x -> shiftL x 1) (add_carry p q))
      (\_ -> (\x -> shiftL x 1 Prelude.+ 1) (succ p))
      y)
    (\p ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> shiftL x 1) (add_carry p q))
      (\q -> (\x -> shiftL x 1 Prelude.+ 1) (add p q))
      (\_ -> (\x -> shiftL x 1) (succ p))
      y)
    (\_ ->
    (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
      (\q -> (\x -> shiftL x 1 Prelude.+ 1) (succ q))
      (\q -> (\x -> shiftL x 1) (succ q))
      (\_ -> (\x -> shiftL x 1 Prelude.+ 1) 1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> (\x -> shiftL x 1 Prelude.+ 1) ((\x -> shiftL x 1) p))
    (\p -> (\x -> shiftL x 1 Prelude.+ 1) (pred_double p))
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
   IsPos p -> IsPos ((\x -> shiftL x 1 Prelude.+ 1) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos ((\x -> shiftL x 1) p);
   x0 -> x0}

double_pred_mask :: Prelude.Integer -> Mask
double_pred_mask x =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> IsPos ((\x -> shiftL x 1) ((\x -> shiftL x 1) p)))
    (\p -> IsPos ((\x -> shiftL x 1) (pred_double p)))
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
      (\_ -> IsPos ((\x -> shiftL x 1) p))
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

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul x y =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p -> add y ((\x -> shiftL x 1) (mul p y)))
    (\p -> (\x -> shiftL x 1) (mul p y))
    (\_ -> y)
    x

iter :: (a1 -> a1) -> a1 -> Prelude.Integer -> a1
iter f x n =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\n' -> f (iter f (iter f x n') n'))
    (\n' -> iter f (iter f x n') n')
    (\_ -> f x)
    n

pow0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow0 x =
  iter (mul x) 1

size_nat :: Prelude.Integer -> Prelude.Integer
size_nat p =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\p0 -> Prelude.succ (size_nat p0))
    (\p0 -> Prelude.succ (size_nat p0))
    (\_ -> Prelude.succ 0)
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

ggcdn :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer -> Prod
         Prelude.Integer (Prod Prelude.Integer Prelude.Integer)
ggcdn n a b =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Pair 1 (Pair a b))
    (\n0 ->
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
             Pair ba aa -> Pair g (Pair aa (add aa ((\x -> shiftL x 1) ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           Pair g p ->
            case p of {
             Pair ab bb -> Pair g (Pair (add bb ((\x -> shiftL x 1) ab)) bb)}}})
        (\b0 ->
        case ggcdn n0 a b0 of {
         Pair g p ->
          case p of {
           Pair aa bb -> Pair g (Pair aa ((\x -> shiftL x 1) bb))}})
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
           Pair aa bb -> Pair g (Pair ((\x -> shiftL x 1) aa) bb)}})
        (\b0 ->
        case ggcdn n0 a0 b0 of {
         Pair g p -> Pair ((\x -> shiftL x 1) g) p})
        (\_ -> Pair 1 (Pair a 1))
        b)
      (\_ -> Pair 1 (Pair 1 b))
      a)
    n

ggcd :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
        (Prod Prelude.Integer Prelude.Integer)
ggcd a b =
  ggcdn ((Prelude.+) (size_nat a) (size_nat b)) a b

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

to_nat :: Prelude.Integer -> Prelude.Integer
to_nat x =
  iter_op (Prelude.+) x (Prelude.succ 0)

of_nat :: Prelude.Integer -> Prelude.Integer
of_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 1)
    (\x ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> 1)
      (\_ -> succ (of_nat x))
      x)
    n

of_succ_nat :: Prelude.Integer -> Prelude.Integer
of_succ_nat n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 1)
    (\x -> succ (of_succ_nat x))
    n

double :: Prelude.Integer -> Prelude.Integer
double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> (\x -> x) ((\x -> shiftL x 1) p))
    (\p -> Prelude.negate ((\x -> shiftL x 1) p))
    x

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (\x -> x) 1)
    (\p -> (\x -> x) ((\x -> shiftL x 1 Prelude.+ 1) p))
    (\p -> Prelude.negate (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate 1)
    (\p -> (\x -> x) (pred_double p))
    (\p -> Prelude.negate ((\x -> shiftL x 1 Prelude.+ 1) p))
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
      (\_ -> (\x -> x) ((\x -> shiftL x 1) p))
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
      (\q -> Prelude.negate ((\x -> shiftL x 1) q))
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

leb :: Prelude.Integer -> Prelude.Integer -> Bool
leb x y =
  case compare0 x y of {
   Gt -> False;
   _ -> True}

ltb :: Prelude.Integer -> Prelude.Integer -> Bool
ltb x y =
  case compare0 x y of {
   Lt -> True;
   _ -> False}

abs :: Prelude.Integer -> Prelude.Integer
abs z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> (\x -> x) p)
    (\p -> (\x -> x) p)
    z

to_nat0 :: Prelude.Integer -> Prelude.Integer
to_nat0 z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 0)
    (\p -> to_nat p)
    (\_ -> 0)
    z

of_nat0 :: Prelude.Integer -> Prelude.Integer
of_nat0 n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> 0)
    (\n0 -> (\x -> x) (of_succ_nat n0))
    n

to_pos :: Prelude.Integer -> Prelude.Integer
to_pos z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> 1)
    (\p -> p)
    (\_ -> 1)
    z

pos_div_eucl :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
                Prelude.Integer
pos_div_eucl a b =
  (\fI fO fH n -> if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))
    (\a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {
       r' = (Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> shiftL x 1) 1)) r)
              ((\x -> x) 1)}
      in
      case ltb r' b of {
       True -> Pair ((Prelude.*) ((\x -> x) ((\x -> shiftL x 1) 1)) q) r';
       False -> Pair
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> shiftL x 1) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = (Prelude.*) ((\x -> x) ((\x -> shiftL x 1) 1)) r} in
      case ltb r' b of {
       True -> Pair ((Prelude.*) ((\x -> x) ((\x -> shiftL x 1) 1)) q) r';
       False -> Pair
        ((Prelude.+) ((Prelude.*) ((\x -> x) ((\x -> shiftL x 1) 1)) q)
          ((\x -> x) 1)) ((Prelude.-) r' b)}})
    (\_ ->
    case leb ((\x -> x) ((\x -> shiftL x 1) 1)) b of {
     True -> Pair 0 ((\x -> x) 1);
     False -> Pair ((\x -> x) 1) 0})
    a

div_eucl :: Prelude.Integer -> Prelude.Integer -> Prod Prelude.Integer
            Prelude.Integer
div_eucl a b =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Pair 0 0)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Pair 0 a)
      (\_ -> pos_div_eucl a' b)
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       Pair q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> Pair (opp q) 0)
          (\_ -> Pair (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.+) b r))
          (\_ -> Pair (opp ((Prelude.+) q ((\x -> x) 1))) ((Prelude.+) b r))
          r})
      b)
    (\a' ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> Pair 0 a)
      (\_ ->
      case pos_div_eucl a' b of {
       Pair q r ->
        (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
          (\_ -> Pair (opp q) 0)
          (\_ -> Pair (opp ((Prelude.+) q ((\x -> x) 1)))
          ((Prelude.-) b r))
          (\_ -> Pair (opp ((Prelude.+) q ((\x -> x) 1))) ((Prelude.-) b r))
          r})
      (\b' ->
      case pos_div_eucl a' ((\x -> x) b') of {
       Pair q r -> Pair q (opp r)})
      b)
    a

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div = (\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)

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

qnum :: Prelude.Rational -> Prelude.Integer
qnum q =
  case q of {
   (:%) qnum0 _ -> qnum0}

qden :: Prelude.Rational -> Prelude.Integer
qden q =
  case q of {
   (:%) _ qden0 -> qden0}

qplus :: Prelude.Rational -> Prelude.Rational -> Prelude.Rational
qplus x y =
  (:%)
    ((Prelude.+) ((Prelude.*) (qnum x) ((\x -> x) (qden y)))
      ((Prelude.*) (qnum y) ((\x -> x) (qden x)))) (mul (qden x) (qden y))

qmult :: Prelude.Rational -> Prelude.Rational -> Prelude.Rational
qmult x y =
  (:%) ((Prelude.*) (qnum x) (qnum y)) (mul (qden x) (qden y))

qopp :: Prelude.Rational -> Prelude.Rational
qopp x =
  (:%) (opp (qnum x)) (qden x)

qminus :: Prelude.Rational -> Prelude.Rational -> Prelude.Rational
qminus x y =
  qplus x (qopp y)

qinv :: Prelude.Rational -> Prelude.Rational
qinv x =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (:%) 0 1)
    (\p -> (:%) ((\x -> x) (qden x)) p)
    (\p -> (:%) (Prelude.negate (qden x)) p)
    (qnum x)

qlt_le_dec :: Prelude.Rational -> Prelude.Rational -> Sumbool
qlt_le_dec x y =
  z_lt_le_dec ((Prelude.*) (qnum x) ((\x -> x) (qden y)))
    ((Prelude.*) (qnum y) ((\x -> x) (qden x)))

qarchimedean :: Prelude.Rational -> Prelude.Integer
qarchimedean q =
  case q of {
   (:%) qnum0 _ ->
    (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
      (\_ -> 1)
      (\p -> add p 1)
      (\_ -> 1)
      qnum0}

qpower_positive :: Prelude.Rational -> Prelude.Integer -> Prelude.Rational
qpower_positive =
  pow_pos qmult

qpower :: Prelude.Rational -> Prelude.Integer -> Prelude.Rational
qpower q z =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> (:%) ((\x -> x) 1) 1)
    (\p -> qpower_positive q p)
    (\p -> qinv (qpower_positive q p))
    z

qabs :: Prelude.Rational -> Prelude.Rational
qabs x =
  case x of {
   (:%) n d -> (:%) (abs n) d}

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

qbound_lt_ZExp2 :: Prelude.Rational -> Prelude.Integer
qbound_lt_ZExp2 q =
  (\fO fP fN n -> if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))
    (\_ -> Prelude.negate ((\x -> shiftL x 1) ((\x -> shiftL x 1)
    ((\x -> shiftL x 1) ((\x -> shiftL x 1 Prelude.+ 1) ((\x -> shiftL x 1)
    ((\x -> shiftL x 1 Prelude.+ 1) ((\x -> shiftL x 1 Prelude.+ 1)
    ((\x -> shiftL x 1 Prelude.+ 1) ((\x -> shiftL x 1 Prelude.+ 1)
    1))))))))))
    (\p ->
    pos_sub (succ (pos_log2floor_plus1 p)) (pos_log2floor_plus1 (qden q)))
    (\_ -> 0)
    (qnum q)

data CReal =
   MkCReal (Prelude.Integer -> Prelude.Rational) Prelude.Integer

seq :: CReal -> Prelude.Integer -> Prelude.Rational
seq c =
  case c of {
   MkCReal seq0 _ -> seq0}

sig_forall_dec :: (Prelude.Integer -> Sumbool) -> Sumor Prelude.Integer
sig_forall_dec =
  Prelude.error "AXIOM TO BE REALIZED"

lowerCutBelow :: (Prelude.Rational -> Bool) -> Prelude.Rational
lowerCutBelow f =
  let {
   s = sig_forall_dec (\n ->
         let {b = f (qopp ((:%) (of_nat0 n) 1))} in
         case b of {
          True -> Right;
          False -> Left})}
  in
  case s of {
   Inleft a -> qopp ((:%) (of_nat0 a) 1);
   Inright -> false_rec}

lowerCutAbove :: (Prelude.Rational -> Bool) -> Prelude.Rational
lowerCutAbove f =
  let {
   s = sig_forall_dec (\n ->
         let {b = f ((:%) (of_nat0 n) 1)} in
         case b of {
          True -> Left;
          False -> Right})}
  in
  case s of {
   Inleft a -> (:%) (of_nat0 a) 1;
   Inright -> false_rec}

type DReal = (Prelude.Rational -> Bool)

dRealQlim_rec :: (Prelude.Rational -> Bool) -> Prelude.Integer ->
                 Prelude.Integer -> Prelude.Rational
dRealQlim_rec f n p =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> false_rec)
    (\n0 ->
    let {
     b = f
           (qplus (proj1_sig (lowerCutBelow f)) ((:%) (of_nat0 n0)
             (of_nat (Prelude.succ n))))}
    in
    case b of {
     True ->
      qplus (proj1_sig (lowerCutBelow f)) ((:%) (of_nat0 n0)
        (of_nat (Prelude.succ n)));
     False -> dRealQlim_rec f n n0})
    p

dRealAbstr :: CReal -> DReal
dRealAbstr x =
  let {
   h = \q n ->
    let {
     s = qlt_le_dec
           (qplus q
             (qpower ((:%) ((\x -> x) ((\x -> shiftL x 1) 1)) 1)
               (opp (of_nat0 n)))) (seq x (opp (of_nat0 n)))}
    in
    case s of {
     Left -> Right;
     Right -> Left}}
  in
  (\q -> case sig_forall_dec (h q) of {
          Inleft _ -> True;
          Inright -> False})

dRealQlim :: DReal -> Prelude.Integer -> Prelude.Rational
dRealQlim x n =
  let {s = lowerCutAbove x} in
  let {s0 = qarchimedean (qminus s (proj1_sig (lowerCutBelow x)))} in
  dRealQlim_rec x n ((Prelude.*) (Prelude.succ n) (to_nat s0))

dRealQlimExp2 :: DReal -> Prelude.Integer -> Prelude.Rational
dRealQlimExp2 x n =
  dRealQlim x (pred (pow (Prelude.succ (Prelude.succ 0)) n))

cReal_of_DReal_seq :: DReal -> Prelude.Integer -> Prelude.Rational
cReal_of_DReal_seq x n =
  proj1_sig (dRealQlimExp2 x (to_nat0 (opp n)))

cReal_of_DReal_scale :: DReal -> Prelude.Integer
cReal_of_DReal_scale x =
  qbound_lt_ZExp2
    (qplus (qabs (cReal_of_DReal_seq x (Prelude.negate 1))) ((:%) ((\x -> x)
      ((\x -> shiftL x 1) 1)) 1))

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

rinv_def :: ()
rinv_def =
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

subtract_dual :: Dual_num -> Dual_num -> Dual_num
subtract_dual x y =
  Mk_dual (( Prelude.- ) (dual_value x) (dual_value y))
    (( Prelude.- ) (dual_deriv x) (dual_deriv y))

negate_dual :: Dual_num -> Dual_num
negate_dual x =
  Mk_dual (((Prelude.-) 0.0) (dual_value x))
    (((Prelude.-) 0.0) (dual_deriv x))

abs_dual :: Dual_num -> Dual_num
abs_dual x =
  Mk_dual (Prelude.abs (dual_value x)) (Prelude.signum (dual_value x))

signum_dual :: Dual_num -> Dual_num
signum_dual x =
  Mk_dual (Prelude.signum (dual_value x)) (Prelude.fromIntegral 0)

from_integer_dual :: Prelude.Integer -> Dual_num
from_integer_dual z =
  Mk_dual (Prelude.fromIntegral z) (Prelude.fromIntegral 0)

multiply_dual :: Dual_num -> Dual_num -> Dual_num
multiply_dual x y =
  Mk_dual (( Prelude.* ) (dual_value x) (dual_value y))
    (( Prelude.+ ) (( Prelude.* ) (dual_deriv x) (dual_value y))
      (( Prelude.* ) (dual_value x) (dual_deriv y)))

divide_dual :: Dual_num -> Dual_num -> Dual_num
divide_dual x y =
  Mk_dual (( Prelude./ ) (dual_value x) (dual_value y))
    (( Prelude./ )
      (( Prelude.- ) (( Prelude.* ) (dual_deriv x) (dual_value y))
        (( Prelude.* ) (dual_value x) (dual_deriv y)))
      ((\ a b -> a Prelude.^ b) (dual_value y) (Prelude.succ (Prelude.succ
        0))))

recip_dual :: Dual_num -> Dual_num
recip_dual x =
  Mk_dual (((Prelude./) 1.0) (dual_value x))
    (( Prelude.* )
      (( Prelude.* ) (Prelude.fromIntegral (Prelude.negate 1))
        (dual_deriv x))
      ((\ a b -> a Prelude.^ b) (((Prelude./) 1.0) (dual_value x))
        (Prelude.succ (Prelude.succ 0))))

acosh_dual :: Dual_num -> Dual_num
acosh_dual d =
  let {x = dual_value d} in
  let {x' = dual_deriv d} in
  Mk_dual (Prelude.acosh x)
  (( Prelude./ ) x'
    (Prelude.sqrt
      (( Prelude.- )
        ((\ a b -> a Prelude.^ b) x (Prelude.succ (Prelude.succ 0)))
        (Prelude.fromIntegral ((\x -> x) 1)))))

from_rational_dual :: Prelude.Rational -> Dual_num
from_rational_dual q =
  Mk_dual (Prelude.fromRational q) (Prelude.fromIntegral 0)

r_to_dual :: R -> Dual_num
r_to_dual x =
  Mk_dual x (Prelude.fromIntegral ((\x -> x) 1))

eval_value :: (Dual_num -> Dual_num) -> R -> R
eval_value f x =
  dual_value (f (r_to_dual x))

eval_derivative :: (Dual_num -> Dual_num) -> R -> R
eval_derivative f x =
  dual_deriv (f (r_to_dual x))

