Require Import vcfloat.VCFloat.


Definition rounded t r:=
(Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
     (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) r).

Definition neg_zero {t: type} := Binary.B754_zero (fprec t) (femax t) true.

Section NAN.

Definition default_rel (t: FPCore.type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs (t: FPCore.type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Lemma default_rel_sep_0 t : 
  default_rel t <> 0.
Proof. 
unfold default_rel; apply Rabs_lt_pos.
rewrite Rabs_pos_eq; [apply Rmult_lt_0_compat; try nra; apply bpow_gt_0 | 
  apply Rmult_le_pos; try nra; apply bpow_ge_0].
Qed.

Lemma default_rel_gt_0 t : 
  0 < default_rel t.
Proof. 
unfold default_rel.
apply Rmult_lt_0_compat; try nra.
apply bpow_gt_0.
Qed.

Lemma default_rel_ge_0 t : 
  0 <= default_rel t.
Proof. apply Rlt_le; apply default_rel_gt_0; auto. Qed.

Lemma default_rel_plus_1_ge_1 t :
1 <= 1 + default_rel t.
Proof. 
rewrite Rplus_comm. 
apply Rcomplements.Rle_minus_l; field_simplify.
apply default_rel_ge_0.
Qed.

Lemma default_abs_gt_0 t : 
  0 < default_abs t.
Proof. 
unfold default_abs.
apply Rmult_lt_0_compat; try nra.
apply bpow_gt_0.
Qed.

Lemma default_abs_ge_0 t :
  0 <= default_abs t.
Proof. apply Rlt_le; apply default_abs_gt_0; auto. Qed.


End NAN.

Definition g (t: type) (n: nat) : R := ((1 + (default_rel t )) ^ n - 1).

Lemma g_pos t n: 
  0 <= g t n. 
Proof. 
unfold g. induction n.
simpl; nra. eapply Rle_trans; [apply IHn| apply Rplus_le_compat; try nra].
simpl. eapply Rle_trans with (1 * (1+default_rel t)^n); try nra.
apply Rmult_le_compat; try nra. rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
field_simplify. apply default_rel_ge_0.
Qed.

Lemma le_g_Sn t n : 
  g t n <= g t (S n).
Proof. 
induction n; unfold g; simpl.
  { field_simplify. apply default_rel_ge_0. }
  unfold g in IHn. eapply Rplus_le_compat; try nra.
  eapply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  rewrite tech_pow_Rmult. apply Rle_pow; try lia.
  rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
  field_simplify; apply default_rel_ge_0. 
Qed.

Lemma d_le_g t n:
default_rel t <= g t (n + 1).
Proof. unfold g. induction n; simpl; field_simplify; try nra.
eapply Rle_trans; [apply IHn|].
apply Rplus_le_compat_r.
replace (default_rel t * (1 + default_rel t) ^ (n + 1) + (1 + default_rel t) ^ (n + 1))
with 
((1 + default_rel t) ^ (n + 1) * (default_rel t  + 1)) by nra.
eapply Rle_trans with ((1 + default_rel t) ^ (n + 1) * 1); try nra.
eapply Rmult_le_compat; try nra.
{ apply pow_le. apply Fourier_util.Rle_zero_pos_plus1. apply default_rel_ge_0. }
apply Rcomplements.Rle_minus_l. field_simplify; apply default_rel_ge_0.
Qed.

Lemma d_le_g_1 t n:
(1<= n)%nat -> default_rel t <= g t n.
Proof. 
intros; unfold g. 
eapply Rle_trans with ((1 + default_rel t)^1 - 1).
field_simplify; nra.
apply Rplus_le_compat; try nra.
apply Rle_pow; try lia.
apply default_rel_plus_1_ge_1.
Qed.


Lemma one_plus_d_mul_g t a n:
  (1 + default_rel t) * g t n * a + default_rel t * a  = g t (n + 1) * a.
Proof. unfold g. rewrite Rmult_minus_distr_l. rewrite tech_pow_Rmult. 
field_simplify. f_equal. rewrite Rmult_comm; repeat f_equal; lia.
Qed.
   

Definition g1 (t: type) (n1: nat) (n2: nat) : R := 
  INR n1 * default_abs t * (1 + g t n2 ).

Lemma g1_pos t n m : 0 <= g1 t n m. 
Proof. unfold g1.
apply Rmult_le_pos; try apply pos_INR.
apply Rmult_le_pos; try apply pos_INR.
apply default_abs_ge_0. unfold g; field_simplify.
apply pow_le.
apply Fourier_util.Rle_zero_pos_plus1.
apply default_rel_ge_0. 
Qed.


Definition error_rel (t: type) (n: nat) (r : R) : R :=
  let e := default_abs t in
  let d := default_rel t in
  if (1 <=? Z.of_nat n) then 
    (g t (n-1)) * (Rabs r + e/d)
  else 0%R.