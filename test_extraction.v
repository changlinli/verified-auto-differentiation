Require Coq.extraction.Extraction.
Extraction Language Haskell.

Require Import Coq.Floats.PrimFloat.

Extract Constant float => "Prelude.Float".

Definition zerof : float := 0.0.

Definition onef : float := 1.0.

Extract Constant zerof => "0.0".

Extract Constant onef => "1.0".

Record dual : Set :=
  { x_value : float
  ; derivative_value : float
  }.

Definition dual_to_float (d : dual) : float :=
  x_value d.

Definition constant(x : float) : dual :=
  {| x_value := x; derivative_value := zerof |}.

Definition identity(x : float) : dual :=
  {| x_value := x; derivative_value := onef |}.

Definition add_dual(x y : dual) : dual :=
  {| x_value := (x_value x) + (x_value y)
  ;  derivative_value := (derivative_value x) + (derivative_value y)
  |}.

Definition multi_dual(x y : dual) : dual :=
  {| x_value := (x_value x) * (x_value y)
  ;  derivative_value := (derivative_value x) * (x_value y) + (derivative_value y) * (x_value x)
  |}.

Definition eval_dual(f : dual -> dual)(x : float) : float :=
  x_value (f ({| x_value := x; derivative_value := 1 |})).

Definition eval_deriv_dual(f : dual -> dual)(x : float) : float :=
  derivative_value (f ({| x_value := x; derivative_value := 1 |})).

Definition times_two(x : dual) : dual :=
  multi_dual (constant 2) x.

Definition two : float :=
  1.0 + 1.0.

Example trivial_example : 1 + 1 = 2.
Proof.
simpl. reflexivity.
Qed.

Example derivative_of_times_two_is_two : eval_deriv_dual times_two 4 = two.
Proof.
reflexivity.
Qed.

Definition multi_by_constant(c : float)(x : dual) : dual :=
  multi_dual x (constant c).

Lemma one_times_anything_is_itself : forall x : float, mul 1 x = x.
Proof.
Admitted.

Lemma zero_times_anything_is_zero : forall x : float, mul zerof x = zerof.
Proof.
Admitted.

Lemma adding_zero_itself : forall x : float, add x 0 = x.
Proof.
Admitted.

Theorem derivative_of_multi_by_constant_is_just_constant
  : forall x c : float, eval_deriv_dual (multi_by_constant c) x = c.
Proof.
intros.
unfold multi_by_constant.
unfold eval_deriv_dual.
simpl.
rewrite one_times_anything_is_itself.
rewrite zero_times_anything_is_zero.
rewrite adding_zero_itself.
reflexivity.
Qed.

Definition not(b : bool) : bool :=
match b with
| true => false
| false => true
end.

Extraction "example.hs" identity.