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