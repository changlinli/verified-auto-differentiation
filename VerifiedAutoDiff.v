Require Import Reals.
Require Import Ranalysis.
Require Import Ranalysis1.
Require Import FunctionalExtensionality.

Open Scope R.

(* Use more standard math terminology *)

Definition derivative_at_point_is (f : R -> R) (x d : R) := derivable_pt_lim f x d.

Definition differentiable_at (f : R -> R) (x : R) := derivable_pt f x.

Definition differentiable (f : R -> R) := derivable f.

Inductive dual_num := mk_dual (num : R) (deriv : R).

Definition dual_value (x : dual_num) : R :=
  match x with
  | mk_dual r _ => r
  end.

Definition dual_deriv (x : dual_num) : R :=
  match x with
  | mk_dual _ r => r
  end.

Definition constant_dual (r : R) (_ : dual_num) : dual_num :=
  mk_dual r 0.

Definition add_dual (x y : dual_num) : dual_num :=
  mk_dual (dual_value x + dual_value y) (dual_deriv x + dual_deriv y).

Definition subtract_dual (x y : dual_num) : dual_num :=
  mk_dual (dual_value x - dual_value y) (dual_deriv x - dual_deriv y).

(* Not sure if this will extract correctly... because total_order_T is an axiom *)
Definition Rsignum (x : R) : R :=
  match total_order_T x 0 with
  | inleft (left _) => - x
  | inleft (right _) => 0
  | inright _ => x
  end.

Definition abs_dual (x : dual_num) : dual_num :=
  mk_dual (Rabs (dual_value x)) (Rsignum (dual_value x)).

Definition signum_dual (x : dual_num) : dual_num :=
  mk_dual (Rsignum (dual_value x)) 0.

Definition from_integer_dual (z : Z) : dual_num :=
  mk_dual (IZR z) 0.

Definition multiply_dual (x y : dual_num) : dual_num :=
  mk_dual
    (dual_value x * dual_value y)
    (dual_deriv x * dual_value y + dual_value x * dual_deriv y).

Definition division_dual (x y : dual_num) : dual_num :=
  mk_dual
    (dual_value x / dual_value y)
    ((dual_deriv x * dual_value y - dual_value x * dual_deriv y) / ((dual_value y)^2)).

Definition recip_dual (x : dual_num) : dual_num :=
  mk_dual (Rinv (dual_value x)) (-1 * (dual_deriv x) * ((Rinv (dual_value x)) ^ 2)).

Definition pi_dual : dual_num :=
  mk_dual PI 0.

Definition exp_dual (exponent : dual_num) : dual_num :=
  mk_dual (exp (dual_value exponent)) (dual_deriv exponent * (exp (dual_value exponent))).

Definition sqrt_dual (x : dual_num) : dual_num :=
  mk_dual (sqrt (dual_value x)) ((dual_deriv x) / (2 * sqrt (dual_value x))).

(*

Because we're not allowing for any partiality, we have to fill in what happens with log when it's
not positive.

Here we clip it to 0.

*)
Definition Rclipped_ln (x : R) : R :=
  match Rle_lt_dec x 0 with
  | left _ => 0
  | right is_pos => Rln (mkposreal x is_pos)
  end.

Definition log_dual (x : dual_num) : dual_num :=
  mk_dual (Rclipped_ln (dual_value x)) (dual_deriv x / dual_value x).

Definition sin_dual (x : dual_num) : dual_num :=
  mk_dual (sin (dual_value x)) (dual_deriv x * cos (dual_value x)).

Definition cos_dual (x : dual_num) : dual_num :=
  mk_dual (cos (dual_value x)) (dual_deriv x * -sin (dual_value x)).

Definition tan_dual (x : dual_num) : dual_num :=
  mk_dual (tan (dual_value x)) ((dual_deriv x) / ((cos (dual_value x)) ^ 2)).


Definition eval_value (f : dual_num -> dual_num) (x : R) : R :=
  dual_value (f (mk_dual x 1)).

Definition eval_derivative (f : dual_num -> dual_num) (x : R) : R :=
  dual_deriv (f (mk_dual x 1)).

Module DifferentiableEverywhere.

Inductive auto_diff_ast :=
  | Var
  | Constant (x : auto_diff_ast) (c : R)
  | Add (x y : auto_diff_ast)
  | Subtract (x y : auto_diff_ast)
  | Multiply (x y : auto_diff_ast)
  | Sin (x : auto_diff_ast)
  | Cos (x : auto_diff_ast)
  | Tan (x : auto_diff_ast).


Fixpoint eval_ast_dual (ast : auto_diff_ast) (x : dual_num) : dual_num :=
  match ast with
  | Add x_ast y_ast => add_dual (eval_ast_dual x_ast x) (eval_ast_dual y_ast x)
  | Var => x
  | Constant x_ast c => constant_dual c (eval_ast_dual x_ast x)
  | Subtract x_ast y_ast => subtract_dual (eval_ast_dual x_ast x) (eval_ast_dual y_ast x)
  | Multiply x_ast y_ast => multiply_dual (eval_ast_dual x_ast x) (eval_ast_dual y_ast x)
  | Sin x_ast => sin_dual (eval_ast_dual x_ast x)
  | Cos x_ast => cos_dual (eval_ast_dual x_ast x)
  | Tan x_ast => tan_dual (eval_ast_dual x_ast x)
  end.

Definition eval_ast_value (ast : auto_diff_ast) (x : R) : R :=
  dual_value (eval_ast_dual ast (mk_dual x 1)).

Definition eval_ast_derivative (ast : auto_diff_ast) (x : R) : R :=
  dual_deriv (eval_ast_dual ast (mk_dual x 1)).


Definition is_well_formed (f : dual_num -> dual_num) : Prop :=
  exists ast : auto_diff_ast, eval_ast_dual ast = f.


(* Simplified version that assumes f is differentiable everywhere *)

Definition derivative_is_correct (f_dual : dual_num -> dual_num) : Prop :=
  let f := eval_value f_dual in
  let f' := eval_derivative f_dual in
  forall x : R, derivative_at_point_is f x (f' x).

(*
More complete version that does not assume f is differentiable everywhere 

Not currently used. Will need to be used if we include division or absolute value.

This is significantly harder to prove though, even if we don't include division or absolute value functions.

Why is that?

Hint: consider whether it's possible for two functions that individually aren't differentiable
at a point to combine and become differentiable there. How does that make the induction in 
auto_differentiate_is_correct harder?
*)
Definition derivative_is_correct' (f_dual : dual_num -> dual_num) : Prop :=
  let f := eval_value f_dual in
  let f' := eval_derivative f_dual in
  forall x : R, differentiable_at f x -> derivative_at_point_is f x (f' x).

Theorem derivative_of_tan : forall x : R, derivative_at_point_is tan x (1 / (cos x) ^ 2).
Admitted.

Theorem multiply_by_one_is_division : forall x c : R, x * (1 / c) = x / c.
Admitted.

Theorem auto_differentiate_is_correct :
  forall f : dual_num -> dual_num, is_well_formed f -> derivative_is_correct f.
Proof.
  intros f H.
  destruct H.
  generalize dependent H.
  generalize dependent f.
  induction x.
  - unfold derivative_is_correct.
    intros.
    rewrite <- H.
    simpl.
    apply derivable_pt_lim_id.
  - unfold derivative_is_correct.
    intros.
    rewrite <- H.
    simpl.
    apply derivable_pt_lim_const.
  - intros.
    rewrite <- H.
    simpl.
    unfold derivative_is_correct.
    unfold derivative_is_correct in IHx1.
    unfold derivative_is_correct in IHx2.
    intros.
    pose proof (IHx1 (eval_ast_dual x1) eq_refl x).
    pose proof (IHx2 (eval_ast_dual x2) eq_refl x).
    apply (derivable_pt_lim_plus _ _ _ _ _ H0 H1).
  - intros.
    rewrite <- H.
    simpl.
    unfold derivative_is_correct.
    unfold derivative_is_correct in IHx1.
    unfold derivative_is_correct in IHx2.
    intros.
    pose proof (IHx1 (eval_ast_dual x1) eq_refl x).
    pose proof (IHx2 (eval_ast_dual x2) eq_refl x).
    apply (derivable_pt_lim_minus _ _ _ _ _ H0 H1).
  - intros.
    rewrite <- H.
    simpl.
    unfold derivative_is_correct.
    unfold derivative_is_correct in IHx1.
    unfold derivative_is_correct in IHx2.
    intros.
    pose proof (IHx1 (eval_ast_dual x1) eq_refl x).
    pose proof (IHx2 (eval_ast_dual x2) eq_refl x).
    apply (derivable_pt_lim_mult _ _ _ _ _ H0 H1).
  - intros.
    rewrite <- H.
    simpl.
    unfold derivative_is_correct.
    intros.
    pose proof (IHx (eval_ast_dual x) eq_refl x0).
    pose proof (derivable_pt_lim_sin (eval_value (eval_ast_dual x) x0)) as sin_deriv.
    pose proof (derivable_pt_lim_comp _ _ _ _ _ H0 sin_deriv) as chain_rule_deriv.
    rewrite Rmult_comm in chain_rule_deriv.
    apply chain_rule_deriv.
  - intros.
    rewrite <- H.
    simpl.
    unfold derivative_is_correct.
    intros.
    pose proof (IHx (eval_ast_dual x) eq_refl x0).
    pose proof (derivable_pt_lim_cos (eval_value (eval_ast_dual x) x0)) as cos_deriv.
    pose proof (derivable_pt_lim_comp _ _ _ _ _ H0 cos_deriv) as chain_rule_deriv.
    rewrite Rmult_comm in chain_rule_deriv.
    apply chain_rule_deriv.
  - intros.
    rewrite <- H.
    simpl.
    unfold derivative_is_correct.
    intros.
    pose proof (IHx (eval_ast_dual x) eq_refl x0).
    pose proof (derivative_of_tan (eval_value (eval_ast_dual x) x0)) as tan_deriv.
    pose proof (derivable_pt_lim_comp _ _ _ _ _ H0 tan_deriv) as chain_rule_deriv.
    rewrite Rmult_comm in chain_rule_deriv.
    rewrite multiply_by_one_is_division in chain_rule_deriv.
    apply chain_rule_deriv.
Qed.

End DifferentiableEverywhere.


Module NotDifferentiableEverywhere.



End NotDifferentiableEverywhere.
