(*This file contains two theorems: forward and backward error bounds for 
  the sum of two floating point lists; the functional model for
  the summation is defined in sum_model.v.*)

Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common sum_model float_acc_lems op_defs list_lemmas.

Require Import Reals.
Open Scope R.

Require Import Sorting Permutation.


Section NAN.
Variable NAN: Nans.

Lemma sum_forward_error :
  forall (t: type) (l: list (ftype t))
  (fs : ftype t) (rs rs_abs : R)
  (Hfs: sum_rel_Ft t l fs)
  (Hrs: sum_rel_R (map FT2R l) rs)
  (Hra: sum_rel_R (map Rabs (map FT2R l)) rs_abs)
  (Hfin: Binary.is_finite (fprec t) (femax t) fs = true),
  Rabs (rs - FT2R fs) <= g t (length l -1) * rs_abs.
Proof.
induction l.
{ intros; unfold g; inversion Hfs; inversion Hrs; subst; simpl;
  rewrite Rminus_0_r, Rabs_R0; nra.  } 
(* case a::l *)
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* case empty l *)
{ subst. inversion Hfs; inversion Hrs.
inversion H2; inversion H6; unfold sum, g; simpl; subst.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
rewrite BPLUS_neg_zero; auto.
field_simplify_Rabs; rewrite Rabs_R0; nra. }
(* case non-empty l *)
inversion Hfs; fold (@sum_rel_Ft NAN t) in H3. 
inversion Hrs; fold sum_rel_R in H7.
inversion Hra; fold sum_rel_R in H11.
subst; unfold sum in *.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
(* IHl *)
specialize (IHl s s0 s1 H3 H7 H11 B).
(* accuracy rewrites *)
assert (Hov: Bplus_no_overflow t (FT2R a) (FT2R s)).
{ unfold Bplus_no_overflow. pose proof is_finite_sum_no_overflow t.
  simpl in H0; unfold rounded in H0; eapply H0; auto. }
destruct (BPLUS_accurate t a A s B Hov) as (d' & Hd'& Hplus); 
rewrite Hplus; clear Hplus Hov.
(* algebra *)
field_simplify_Rabs.
replace (- FT2R a * d' + s0 - FT2R s * d' - FT2R s) with
  ((s0 - FT2R s) - d' * (FT2R s + FT2R a)) by nra.
eapply Rle_trans; 
  [ apply Rabs_triang | eapply Rle_trans; [ apply Rplus_le_compat_r
    | rewrite !Rabs_Ropp] ].
apply IHl.
eapply Rle_trans; 
  [apply Rplus_le_compat_l | ].
  rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
  apply Hd'.
  eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat_r].
  rewrite Rabs_minus_sym in IHl; apply Rabs_le_minus in IHl. apply IHl.
rewrite !Rmult_plus_distr_l; rewrite <- !Rplus_assoc.
replace (g t (length l - 1) * s1 + default_rel t * (g t (length l - 1) * s1)) with
  ((1+ default_rel t) * g t (length l - 1) * s1) by nra.
eapply Rle_trans; [apply Rplus_le_compat_r; 
  apply Rplus_le_compat_l; apply Rmult_le_compat_l; try apply Rabs_pos|].
apply default_rel_ge_0.
apply (sum_rel_R_Rabs (map FT2R l)); auto; apply H11.
rewrite (sum_rel_R_Rabs_eq (map FT2R l)); auto.
rewrite one_plus_d_mul_g. simpl.
rewrite Rplus_comm.
apply length_not_empty in H; auto.
apply Rplus_le_compat.
apply Rmult_le_compat; try apply Rabs_pos; 
  try apply default_rel_ge_0; try nra.
apply d_le_g_1; rewrite Nat.sub_0_r; auto.
rewrite Nat.sub_0_r; apply Req_le; f_equal. 
rewrite Nat.sub_add; auto. 
Qed.

Lemma sum_backward_error :
  forall (t: type) (l: list (ftype t))
  (fs : ftype t)
  (Hfs: sum_rel_Ft t l fs)
  (Hfin: Binary.is_finite (fprec t) (femax t) fs = true),
    exists (l': list R), 
    length l' = length l /\
    sum_rel_R l' (FT2R fs) /\
    (forall n, (n <= length l')%nat -> exists delta, 
        nth n l' 0 = FT2R (nth n l neg_zero) * (1 + delta) /\ Rabs delta <= g t (length l' - 1)).
Proof.
intros ? ?. induction l.
{ intros; exists []; repeat split; auto. 
  inversion Hfs; subst; simpl. apply sum_rel_nil.
  intros. simpl in H; assert (n = 0)%nat by lia; subst.
  exists 0; split; [simpl; nra| unfold g; rewrite Rabs_R0; simpl; nra].
}
(* case a::l *)
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* case empty l *)
{ subst; inversion Hfs; subst; unfold sum in *. 
  destruct (BPLUS_finite_e _ _ Hfin).
  inversion H2; subst. exists [FT2R a]; split; [ simpl; auto | split ; 
  [unfold sum; rewrite BPLUS_neg_zero; [apply sum_rel_R_single'| auto]|] ].  
  intros. exists 0; simpl in H1; split; 
  [assert ((n = 1)%nat \/ (n = 0)%nat) by lia; destruct H3; subst; simpl; nra|].
  rewrite Rabs_R0; simpl; unfold g; nra.
}
(* case non-empty l *)
inversion Hfs; fold (@sum_rel_Ft NAN t) in H3. 
subst; unfold sum in *.
  destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
(* IHl *)
pose proof (length_not_empty_nat l H) as Hlen1.
specialize (IHl s H3 B).
destruct IHl as (l' & Hlen' & Hsum & Hdel).
(* construct l'0 *)
assert (Hov: Bplus_no_overflow t (FT2R a) (FT2R s)).
{ unfold Bplus_no_overflow. pose proof is_finite_sum_no_overflow t.
  simpl in H0; unfold rounded in H0; eapply H0; auto. }
pose proof (BPLUS_accurate t a A s B Hov) as Hplus.
destruct Hplus as (d' & Hd'& Hplus).
exists (FT2R a * (1+d') :: map (Rmult (1+d')) l'); repeat split.
{ simpl; auto. rewrite map_length; auto. }
{ rewrite Hplus. unfold sum_rel_R. 
  rewrite Rmult_plus_distr_r. apply sum_rel_cons. rewrite Rmult_comm; apply sum_map_Rmult; auto. }
intros. destruct n. 
{ simpl. exists d'; split; auto.
  eapply Rle_trans; [apply Hd'| ]. apply d_le_g_1. rewrite map_length; auto.
  rewrite Hlen'. lia. }
simpl in H0; rewrite map_length in H0; rewrite Hlen' in H0.
assert (Hlen2: (n <= length l')%nat) by lia.
specialize (Hdel n Hlen2).
destruct Hdel as (d & Hd1 & Hd2).
exists ( (1+d') * (1+d) -1). simpl; split.
{ replace 0 with (Rmult (1 + d') 0) by nra. rewrite map_nth; rewrite Hd1; nra. }
rewrite map_length. field_simplify_Rabs. 
  eapply Rle_trans; [apply Rabs_triang | eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang | ]  ].
rewrite Rabs_mult.
replace (Rabs d' * Rabs d + Rabs d' + Rabs d ) with
  ((1 + Rabs d') * Rabs d + Rabs d' ) by nra.
eapply Rle_trans; [apply Rplus_le_compat | ].
apply Rmult_le_compat; try apply Rabs_pos.
apply Fourier_util.Rle_zero_pos_plus1; try apply Rabs_pos.
apply Rplus_le_compat_l; apply Hd'.
apply Hd2. apply Hd'.
replace ((1 + default_rel t) * g t (length l' - 1) + default_rel t) with
((1 + default_rel t) * g t (length l' - 1) * 1 + default_rel t * 1) by nra.
rewrite one_plus_d_mul_g; apply Req_le; rewrite Rmult_1_r. f_equal; lia.
Qed.


(* if the forward error of the floating-point dot product of a list respects a bound, then
  the forward error of a permutation of  that list respects the same bound *)
Lemma sum_forward_error_permute :
  forall (t: type) (l l0: list (ftype t))
  (Hper: Permutation l l0)
  (fs fs0: ftype t) (rs rs_abs: R)
  (Hfs: sum_rel_Ft t l fs)
  (Hfs0: sum_rel_Ft t l0 fs0)
  (Hrs: sum_rel_R (map FT2R l) rs)
  (Hra: sum_rel_R (map Rabs (map FT2R l)) rs_abs)
  (Hfin: Binary.is_finite (fprec t) (femax t) fs = true)
  (Hfin0: Binary.is_finite (fprec t) (femax t) fs0 = true),
  Rabs (rs - FT2R fs0) <= g t (length l0 -1) * rs_abs.
Proof.
intros.
apply sum_forward_error; auto.
{ eapply sum_rel_R_permute_t. apply Hper. auto. }
apply (sum_rel_R_permute (map Rabs (map FT2R l)) (map Rabs (map FT2R l0))).
repeat apply Permutation_map; auto.
auto.
Qed.


End NAN.