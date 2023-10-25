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

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

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

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add1 :: Positive -> Positive -> Positive
add1 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add1 p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add1 p q);
     XO q -> XO (add1 p q);
     XH -> XI p};
   XH -> case y of {
          XI q -> XO (succ q);
          XO q -> XI q;
          XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add1 p q);
     XH -> XO (succ p)};
   XH -> case y of {
          XI q -> XI (succ q);
          XO q -> XO (succ q);
          XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double p));
   XH -> IsNul}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH -> case y of {
          XH -> IsNul;
          _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul1 :: Positive -> Positive -> Positive
mul1 x y =
  case x of {
   XI p -> add1 y (XO (mul1 p y));
   XO p -> XO (mul1 p y);
   XH -> y}

size_nat :: Positive -> Nat
size_nat p =
  case p of {
   XI p0 -> S (size_nat p0);
   XO p0 -> S (size_nat p0);
   XH -> S O}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH -> case y of {
          XH -> r;
          _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

ggcdn :: Nat -> Positive -> Positive -> Prod Positive
         (Prod Positive Positive)
ggcdn n a b =
  case n of {
   O -> Pair XH (Pair a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> Pair a (Pair XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           Pair g p ->
            case p of {
             Pair ba aa -> Pair g (Pair aa (add1 aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           Pair g p ->
            case p of {
             Pair ab bb -> Pair g (Pair (add1 bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         Pair g p -> case p of {
                      Pair aa bb -> Pair g (Pair aa (XO bb))}};
       XH -> Pair XH (Pair a XH)};
     XO a0 ->
      case b of {
       XI _ ->
        case ggcdn n0 a0 b of {
         Pair g p -> case p of {
                      Pair aa bb -> Pair g (Pair (XO aa) bb)}};
       XO b0 -> case ggcdn n0 a0 b0 of {
                 Pair g p -> Pair (XO g) p};
       XH -> Pair XH (Pair a XH)};
     XH -> Pair XH (Pair XH b)}}

ggcd :: Positive -> Positive -> Prod Positive (Prod Positive Positive)
ggcd a b =
  ggcdn (add (size_nat a) (size_nat b)) a b

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op add x (S O)

of_nat :: Nat -> Positive
of_nat n =
  case n of {
   O -> XH;
   S x -> case x of {
           O -> XH;
           S _ -> succ (of_nat x)}}

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x -> succ (of_succ_nat x)}

double :: Z -> Z
double x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double :: Z -> Z
succ_double x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double (pos_sub p q);
     XO q -> succ_double (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add2 :: Z -> Z -> Z
add2 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add1 x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add1 x' y')}}

opp :: Z -> Z
opp x =
  case x of {
   Z0 -> Z0;
   Zpos x0 -> Zneg x0;
   Zneg x0 -> Zpos x0}

sub0 :: Z -> Z -> Z
sub0 m n =
  add2 m (opp n)

mul2 :: Z -> Z -> Z
mul2 x y =
  case x of {
   Z0 -> Z0;
   Zpos x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zpos (mul1 x' y');
     Zneg y' -> Zneg (mul1 x' y')};
   Zneg x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zneg (mul1 x' y');
     Zneg y' -> Zpos (mul1 x' y')}}

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 -> case y of {
          Z0 -> Eq;
          Zpos _ -> Lt;
          Zneg _ -> Gt};
   Zpos x' -> case y of {
               Zpos y' -> compare x' y';
               _ -> Gt};
   Zneg x' -> case y of {
               Zneg y' -> compOpp (compare x' y');
               _ -> Lt}}

sgn :: Z -> Z
sgn z =
  case z of {
   Z0 -> Z0;
   Zpos _ -> Zpos XH;
   Zneg _ -> Zneg XH}

max :: Z -> Z -> Z
max n m =
  case compare0 n m of {
   Lt -> m;
   _ -> n}

abs :: Z -> Z
abs z =
  case z of {
   Zneg p -> Zpos p;
   x -> x}

to_nat0 :: Z -> Nat
to_nat0 z =
  case z of {
   Zpos p -> to_nat p;
   _ -> O}

of_nat0 :: Nat -> Z
of_nat0 n =
  case n of {
   O -> Z0;
   S n0 -> Zpos (of_succ_nat n0)}

to_pos :: Z -> Positive
to_pos z =
  case z of {
   Zpos p -> p;
   _ -> XH}

ggcd0 :: Z -> Z -> Prod Z (Prod Z Z)
ggcd0 a b =
  case a of {
   Z0 -> Pair (abs b) (Pair Z0 (sgn b));
   Zpos a0 ->
    case b of {
     Z0 -> Pair (abs a) (Pair (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zpos aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zpos aa) (Zneg bb))}}};
   Zneg a0 ->
    case b of {
     Z0 -> Pair (abs a) (Pair (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zneg aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zneg aa) (Zneg bb))}}}}

z_lt_dec :: Z -> Z -> Sumbool
z_lt_dec x y =
  case compare0 x y of {
   Lt -> Left;
   _ -> Right}

z_lt_ge_dec :: Z -> Z -> Sumbool
z_lt_ge_dec =
  z_lt_dec

z_lt_le_dec :: Z -> Z -> Sumbool
z_lt_le_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_lt_ge_dec x y)

pow_pos :: (a1 -> a1 -> a1) -> a1 -> Positive -> a1
pow_pos rmul x i =
  case i of {
   XI i0 -> let {p = pow_pos rmul x i0} in rmul x (rmul p p);
   XO i0 -> let {p = pow_pos rmul x i0} in rmul p p;
   XH -> x}

data Q =
   Qmake Z Positive

qnum :: Q -> Z
qnum q =
  case q of {
   Qmake qnum0 _ -> qnum0}

qden :: Q -> Positive
qden q =
  case q of {
   Qmake _ qden0 -> qden0}

qplus :: Q -> Q -> Q
qplus x y =
  Qmake
    (add2 (mul2 (qnum x) (Zpos (qden y))) (mul2 (qnum y) (Zpos (qden x))))
    (mul1 (qden x) (qden y))

qmult :: Q -> Q -> Q
qmult x y =
  Qmake (mul2 (qnum x) (qnum y)) (mul1 (qden x) (qden y))

qopp :: Q -> Q
qopp x =
  Qmake (opp (qnum x)) (qden x)

qminus :: Q -> Q -> Q
qminus x y =
  qplus x (qopp y)

qinv :: Q -> Q
qinv x =
  case qnum x of {
   Z0 -> Qmake Z0 XH;
   Zpos p -> Qmake (Zpos (qden x)) p;
   Zneg p -> Qmake (Zneg (qden x)) p}

qlt_le_dec :: Q -> Q -> Sumbool
qlt_le_dec x y =
  z_lt_le_dec (mul2 (qnum x) (Zpos (qden y))) (mul2 (qnum y) (Zpos (qden x)))

qarchimedean :: Q -> Positive
qarchimedean q =
  case q of {
   Qmake qnum0 _ -> case qnum0 of {
                     Zpos p -> add1 p XH;
                     _ -> XH}}

qpower_positive :: Q -> Positive -> Q
qpower_positive =
  pow_pos qmult

qpower :: Q -> Z -> Q
qpower q z =
  case z of {
   Z0 -> Qmake (Zpos XH) XH;
   Zpos p -> qpower_positive q p;
   Zneg p -> qinv (qpower_positive q p)}

qabs :: Q -> Q
qabs x =
  case x of {
   Qmake n d -> Qmake (abs n) d}

pos_log2floor_plus1 :: Positive -> Positive
pos_log2floor_plus1 p =
  case p of {
   XI p' -> succ (pos_log2floor_plus1 p');
   XO p' -> succ (pos_log2floor_plus1 p');
   XH -> XH}

qbound_lt_ZExp2 :: Q -> Z
qbound_lt_ZExp2 q =
  case qnum q of {
   Z0 -> Zneg (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))));
   Zpos p ->
    pos_sub (succ (pos_log2floor_plus1 p)) (pos_log2floor_plus1 (qden q));
   Zneg _ -> Z0}

data CReal =
   MkCReal (Z -> Q) Z

seq :: CReal -> Z -> Q
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
         let {b = f (qopp (Qmake (of_nat0 n) XH))} in
         case b of {
          True -> Right;
          False -> Left})}
  in
  case s of {
   Inleft a -> qopp (Qmake (of_nat0 a) XH);
   Inright -> false_rec}

lowerCutAbove :: (Q -> Bool) -> Q
lowerCutAbove f =
  let {
   s = sig_forall_dec (\n ->
         let {b = f (Qmake (of_nat0 n) XH)} in
         case b of {
          True -> Left;
          False -> Right})}
  in
  case s of {
   Inleft a -> Qmake (of_nat0 a) XH;
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
           (qplus q (qpower (Qmake (Zpos (XO XH)) XH) (opp (of_nat0 n))))
           (seq x (opp (of_nat0 n)))}
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

cReal_of_DReal_seq :: DReal -> Z -> Q
cReal_of_DReal_seq x n =
  proj1_sig (dRealQlimExp2 x (to_nat0 (opp n)))

cReal_of_DReal_scale :: DReal -> Z
cReal_of_DReal_scale x =
  qbound_lt_ZExp2
    (qplus (qabs (cReal_of_DReal_seq x (Zneg XH))) (Qmake (Zpos (XO XH)) XH))

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

eval_derivative :: (Dual_num -> Dual_num) -> R -> R
eval_derivative f x =
  dual_deriv (f (Mk_dual x (Prelude.fromIntegral (Zpos XH))))

