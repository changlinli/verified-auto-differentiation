Require Import Reals.
Require Import Ranalysis.
Require Import Ranalysis1.

Open Scope R.

Check continuity_plus.

Lemma identity_is_continuous : continuity id.
Proof.
unfold continuity.
intros.
unfold continuity_pt.
unfold continue_in.
unfold limit1_in.
unfold limit_in.
simpl.
intros.
exists eps.
split.
+ assumption.
+ intros. unfold id. destruct H0. apply H1.
Qed.

Lemma zero_squared_is_zero : 0 ^ 2 = 0.
Proof.
unfold pow.
rewrite Rmult_comm.
rewrite Rmult_0_r.
reflexivity.
Qed.

Lemma one_is_greater_than_zero : 1 > 0.
Proof.
pose proof (plus_Rsqr_gt_0 0).
rewrite zero_squared_is_zero in H.
rewrite Rplus_0_r in H.
apply H.
Qed.

Lemma dist_on_same_point_is_zero : forall (M : Metric_Space) (x : Base M), dist M x x = 0.
Proof.
intros.
pose proof (eq_refl x).
rewrite <- dist_refl in H.
apply H.
Qed.

Lemma constant_is_continuous : forall c : R, continuity (fun _ => c).
Proof.
unfold continuity.
intros.
unfold continuity_pt.
unfold continue_in.
unfold limit1_in.
unfold limit_in.
intros.
exists 1. (* this doesn't matter, it could be any value *)
split.
+ apply one_is_greater_than_zero.
+ intros. rewrite dist_on_same_point_is_zero. apply H.
Qed.

(* Use more standard math terminology *)

Definition derivative_at_point_is (f : R -> R) (x d : R) := derivable_pt_lim f x d.

Definition differentiable_at (f : R -> R) (x : R) := derivable_pt f x.

Definition differentiable (f : R -> R) := derivable f.

Inductive auto_diff_ast :=
  | Var (x : R)
  | Constant (x : auto_diff_ast) (c : R)
  | Add (x y : auto_diff_ast)
  | Subtract (x y : auto_diff_ast).

Inductive dual_num := mk_dual (num : R) (deriv : R).

Definition constant_dual (r : R) (_ : dual_num) : dual_num :=
  mk_dual r 0.

Definition add_dual (x y : dual_num) : dual_num :=
  match x, y with
  | (mk_dual x_val x_deriv), (mk_dual y_val y_deriv) => mk_dual (x_val + y_val) (x_deriv + y_deriv)
  end.

(* 
Definition my_ast : auto_diff_ast.

Definition my_f : dual_num -> dual_num := eval_ast_dual my_ast.
*)

Fixpoint eval_ast_dual (ast : auto_diff_ast) (x : dual_num) : dual_num :=
  match ast with
  | Add x_ast y_ast => add_dual (eval_ast_dual x_ast x) (eval_ast_dual y_ast x)
  | Var _ => _
  | Constant x_ast c => constant_dual c (eval_ast_dual x_ast x)
  | Subtract _ _ => _
  end.

Definition eval_ast_value (ast : auto_diff_ast) (x : R) : R. Admitted.

Definition eval_ast_derivative (ast : auto_diff_ast) (x : R) : R. Admitted.

Definition eval_value (f : dual_num -> dual_num) (x : R) : R. Admitted.

Definition eval_derivative (f : dual_num -> dual_num) (x : R) : R. Admitted.

Definition is_well_formed (f : dual_num -> dual_num) : Prop :=
  exists ast : auto_diff_ast, eval_ast_dual ast = f.

Definition derivative_is_correct (f_dual : dual_num -> dual_num) : Prop :=
  let f := eval_value f_dual in
  let f' := eval_derivative f_dual in
  forall x : R, differentiable_at f x -> derivative_at_point_is f x (f' x).

Theorem auto_differentiate_is_correct :
  forall f : dual_num -> dual_num, is_well_formed f -> derivative_is_correct f.
  Admitted.