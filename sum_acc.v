Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common sum_model float_acc_lems op_defs list_lemmas.

Require Import Reals.
Open Scope R.

Definition error_rel (t: type) (n : nat) (r : R) : R :=
  let e := default_abs t in
  let d := default_rel t in
  if (1 <=? Z.of_nat n) then 
    ((1 + d)^(n-1) - 1) * (Rabs r + e/d)
  else 0%R.

Section NAN.
Variable NAN: Nans.

Lemma sum_mixed_error :
  forall (t: type) (l: list (ftype t))
  (Hlen: (1 <= length l)%nat)
  (fs : ftype t) (rs rs_abs : R)
  (Hfs: sum_rel_Ft t l fs)
  (Hrs: sum_rel_R (map FT2R l) rs)
  (Hra: sum_rel_R (map Rabs (map FT2R l)) rs_abs)
  (Hin: forall a, In a l ->  Binary.is_finite _ _ a = true)
  (Hfin: Binary.is_finite (fprec t) (femax t) fs = true),
  Rabs (rs - FT2R fs) <= g t (length l -1) * rs_abs.
Proof.
induction l.
{ intros. inversion Hfs; inversion Hrs; inversion Hra; unfold g; subst; simpl.
  rewrite Rminus_0_r; rewrite Rabs_R0; nra. }
(* case a::l *)
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* case empty l *)
{ assert (HFINa: 
  Binary.is_finite (fprec t) (femax t) a = true) by (apply Hin; simpl; auto).
  assert (HFINfs: 
  Binary.is_finite (fprec t) (femax t) fs = true).
  { subst. inversion Hfs. fold (@sum_rel_Ft NAN t) in H2. inversion H2. subst.
  destruct a; simpl; try discriminate; auto. } 
  subst; simpl; pose proof (sum_rel_Ft_single t fs a HFINfs Hfs); subst.
  rewrite (sum_rel_R_single (FT2R a) rs Hrs); subst.
  unfold g; simpl; field_simplify_Rabs;
  rewrite Rabs_R0; nra. }
(* case non-empty l *)
inversion Hfs; fold (@sum_rel_Ft NAN t) in H3. 
inversion Hrs; fold sum_rel_R in H7.
inversion Hra; fold sum_rel_R in H11.
subst; unfold sum in *.
assert (HFINa: 
  Binary.is_finite (fprec t) (femax t) a = true) by (apply Hin; simpl; auto).
(* IHl *)
pose proof (length_not_empty_nat l H) as Hlen1.
assert (Hinl: forall a : ftype t,
       In a l -> Binary.is_finite (fprec t) (femax t) a = true).
{ intros; apply Hin; simpl; auto. }
assert (Hfins: Binary.is_finite (fprec t) (femax t) s = true).
{ destruct a, s; simpl in *; try discriminate; auto. }
specialize (IHl Hlen1 s s0 s1 H3 H7 H11 Hinl Hfins).
(* accuracy rewrites *)
assert (Hov: Bplus_no_overflow t (FT2R a) (FT2R s)).
{ unfold Bplus_no_overflow. pose proof is_finite_sum_no_overflow t.
  simpl in H0; unfold rounded in H0; eapply H0; auto. auto. }
pose proof (BPLUS_accurate t a HFINa s Hfins Hov) as Hplus.
destruct Hplus as (d' & Hd'& Hplus); rewrite Hplus; 
  clear Hplus Hov.
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
apply Rplus_le_compat.
apply Rmult_le_compat; try apply Rabs_pos; 
  try apply default_rel_ge_0; try nra.
apply d_le_g_1; try lia.
apply Req_le; f_equal. f_equal; lia.
Qed.


End NAN.