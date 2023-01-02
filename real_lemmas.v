Require Import List.
Import ListNotations.
Require Import Reals.
From Coquelicot Require Import Coquelicot.

Open Scope R.

Import Lra.

Lemma fold_left_Rplus_Rplus:
 forall al b c, fold_left Rplus al (b+c) = c + fold_left Rplus al b.
Proof.
intros.
rewrite ! fold_symmetric by (intros; lra).
induction al; simpl; intros; lra.
Qed.

Lemma fold_left_Rplus_0:
 forall al b , fold_left Rplus al b = b + fold_left Rplus al 0.
Proof.
intros.
rewrite ! fold_symmetric by (intros; lra).
induction al; simpl; intros; lra.
Qed.

Lemma length_not_empty_lt {A} l :
l <> [] -> 
0 < INR (@length A l).
Proof.
intros.
destruct l.
destruct H; auto.
simpl (length (a:: l)).
rewrite <- Nat.add_1_r.
rewrite plus_INR.
apply Rcomplements.Rlt_minus_l.
field_simplify.
simpl.
eapply Rlt_le_trans with 0;  try nra.
apply pos_INR.
Qed.

Lemma length_not_empty_nat' {A} l :
l <> [] -> 
(0 <= (@length A l))%nat.
Proof.
intros.
apply INR_le.
apply Rlt_le.
apply length_not_empty_lt;auto.
Qed.

Close Scope R.