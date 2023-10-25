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

Inductive dual_num := mk_dual (num : R) (deriv : R).

Definition dual_value (x : dual_num) : R :=
  match x with
  | mk_dual r _ => r
  end.

Definition dual_deriv (x : dual_num) : R :=
  match x with
  | mk_dual _ r => r
  end.

Inductive auto_diff_ast :=
  | Var
  | Constant (x : auto_diff_ast) (c : R)
  | Add (x y : auto_diff_ast)
  | Subtract (x y : auto_diff_ast).

Definition constant_dual (r : R) (_ : dual_num) : dual_num :=
  mk_dual r 0.

Definition add_dual (x y : dual_num) : dual_num :=
  mk_dual (dual_value x + dual_value y) (dual_deriv x + dual_deriv y).

Definition subtract_dual (x y : dual_num) : dual_num :=
  mk_dual (dual_value x - dual_value y) (dual_deriv x - dual_deriv y).

(*
Definition my_ast : auto_diff_ast.

Definition my_f : dual_num -> dual_num := eval_ast_dual my_ast.
    Add
      Var
        x
      Var
        x
*)

Fixpoint eval_ast_dual (ast : auto_diff_ast) (x : dual_num) : dual_num :=
  match ast with
  | Add x_ast y_ast => add_dual (eval_ast_dual x_ast x) (eval_ast_dual y_ast x)
  | Var => x
  | Constant x_ast c => constant_dual c (eval_ast_dual x_ast x)
  | Subtract x_ast y_ast => subtract_dual (eval_ast_dual x_ast x) (eval_ast_dual y_ast x)
  end.

Definition eval_ast_value (ast : auto_diff_ast) (x : R) : R :=
  dual_value (eval_ast_dual ast (mk_dual x 1)).

Definition eval_ast_derivative (ast : auto_diff_ast) (x : R) : R :=
  dual_deriv (eval_ast_dual ast (mk_dual x 1)).

Definition eval_value (f : dual_num -> dual_num) (x : R) : R :=
  dual_value (f (mk_dual x 1)).

Definition eval_derivative (f : dual_num -> dual_num) (x : R) : R :=
  dual_deriv (f (mk_dual x 1)).

Definition is_well_formed (f : dual_num -> dual_num) : Prop :=
  exists ast : auto_diff_ast, eval_ast_dual ast = f.


(* Simplified version that assumes f is differentiable everywhere *)
Definition derivative_is_correct (f_dual : dual_num -> dual_num) : Prop :=
  let f := eval_value f_dual in
  let f' := eval_derivative f_dual in
  forall x : R, derivative_at_point_is f x (f' x).

(*
More complete version that does not assume f is differentiable everywhere 

Not currently used. Will need to be used if we include division.  
*)
Definition derivative_is_correct' (f_dual : dual_num -> dual_num) : Prop :=
  let f := eval_value f_dual in
  let f' := eval_derivative f_dual in
  forall x : R, differentiable_at f x -> derivative_at_point_is f x (f' x).

Lemma eval_value_id_is_id : eval_value (fun x => x) = id.
Proof.
unfold eval_value.
reflexivity.
Qed.

Lemma eval_deriv_id_is_1 : forall r : R, eval_derivative (fun x => x) r = 1.
Proof.
  unfold eval_derivative.
  reflexivity.
Qed.

Lemma eval_value_const_is_const :
  forall c,
  eval_value (constant_dual c) = fct_cte c.
Proof.
  intros c.
  unfold eval_value.
  simpl.
  reflexivity.
Qed.

Lemma eval_deriv_const_is_0 : forall c r, eval_derivative (constant_dual c) r = 0.
Proof.
  unfold eval_derivative.
  reflexivity.
Qed.

Lemma constant_ignores_arg : forall c x,
  (fun x1 : dual_num => constant_dual c (eval_ast_dual x x1)) = (constant_dual c).
Proof.
  intros c x.
  unfold constant_dual.
  reflexivity.
Qed.

Lemma eval_value_add_is_add :
  forall f g : dual_num -> dual_num,
  eval_value (fun x => add_dual (f x) (g x)) =
    fun x => eval_value f x + eval_value g x.
Proof.
reflexivity.
Qed.

Lemma eval_deriv_add_is_add :
  forall f g : dual_num -> dual_num,
  eval_derivative (fun x => add_dual (f x) (g x)) =
    fun x => eval_derivative f x + eval_derivative g x.
Proof.
reflexivity.
Qed.

Lemma eval_value_subtract_is_subtract :
  forall f g : dual_num -> dual_num,
  eval_value (fun x => subtract_dual (f x) (g x)) =
    fun x => eval_value f x - eval_value g x.
Proof.
reflexivity.
Qed.

Lemma eval_deriv_subtract_is_subtract :
  forall f g : dual_num -> dual_num,
  eval_derivative (fun x => subtract_dual (f x) (g x)) =
    fun x => eval_derivative f x - eval_derivative g x.
Proof.
reflexivity.
Qed.

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
    rewrite eval_value_id_is_id.
    rewrite eval_deriv_id_is_1.
    apply derivable_pt_lim_id.
  - unfold derivative_is_correct.
    intros.
    rewrite <- H.
    simpl.
    rewrite constant_ignores_arg.
    rewrite eval_value_const_is_const.
    rewrite eval_deriv_const_is_0.
    apply derivable_pt_lim_const.
  - intros.
    rewrite <- H.
    simpl.
    unfold derivative_is_correct.
    unfold derivative_is_correct in IHx1.
    unfold derivative_is_correct in IHx2.
    intros.
    rewrite eval_value_add_is_add.
    rewrite eval_deriv_add_is_add.
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
    rewrite eval_value_subtract_is_subtract.
    rewrite eval_deriv_subtract_is_subtract.
    pose proof (IHx1 (eval_ast_dual x1) eq_refl x).
    pose proof (IHx2 (eval_ast_dual x2) eq_refl x).
    apply (derivable_pt_lim_minus _ _ _ _ _ H0 H1).
Qed.
