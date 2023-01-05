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

Lemma prove_rndoff_sum (t : type) :
  forall (l : list (ftype t)) fs rs rs_abs,
  sum_rel_Ft t l fs -> sum_rel_R (map FT2R l) rs -> 
      sum_rel_R (map Rabs (map FT2R l)) rs_abs ->
  let ov := bpow Zaux.radix2 (femax t) in
  (forall a, In a l ->  Binary.is_finite _ _ a = true) ->
  (forall x y , BPLUS t x y = fs  -> Binary.is_finite _ _ fs = true /\
          Rabs (rounded t (FT2R x + FT2R y)) < ov) -> 
  Binary.is_finite (fprec t) (femax t) fs = true /\
  Rabs (rs - FT2R fs) <= error_rel t (length l) rs_abs.
Proof.
induction l.
-
intros.
repeat split.
+ inversion H; simpl; auto.
+ intros.
  inversion H; subst; clear H;
  inversion H0; subst; clear H0; simpl.
  cbv [error_rel]; simpl.
  rewrite Rminus_0_r;
  rewrite Rabs_R0;
  nra.
-
intros  ? ? ? Hf Hr Hra ? Hin.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
+
assert (HFINa: 
  Binary.is_finite (fprec t) (femax t) a = true) by (apply Hin; simpl; auto).
assert (HFINfs: 
  Binary.is_finite (fprec t) (femax t) fs = true).
  { subst. inversion Hf. fold (@sum_rel_Ft NAN t) in H2. inversion H2. subst.
  destruct a; simpl; try discriminate; auto.
  destruct s; simpl; auto.
  }
split; auto.
* intros; subst; simpl. pose proof (sum_rel_Ft_single t fs a HFINfs Hf).
  rewrite (sum_rel_R_single (FT2R a) rs Hr); subst.
  cbv [error_rel]; simpl.
  field_simplify_Rabs.
  rewrite Rabs_R0.
  field_simplify; try nra. apply default_rel_sep_0.
(* case non-empty l *)
+
intros; inversion Hf.
fold (@sum_rel_Ft NAN t) in H4. 
inversion Hr. fold sum_rel_R in H8.
inversion Hra. fold sum_rel_R in H12.
clear H1 H3 H5 H7 H9 H11 a1 a2 l2 l1 a0 l0 Hf Hr Hra.
assert (HFINa: 
  Binary.is_finite (fprec t) (femax t) a = true) by (apply Hin; simpl; auto).
(* IHl *)
assert (Hinl: forall a : ftype t,
       In a l -> Binary.is_finite (fprec t) (femax t) a = true).
{ intros; apply Hin; simpl; auto.
}
unfold sum in *.
specialize (H0 a s H2).
destruct H0 as (HFINfs & HOVfs).
assert (H0: forall x y : ftype t,
       BPLUS t x y = s -> Binary.is_finite (fprec t) (femax t) s = true /\
       Rabs (rounded t (FT2R x + FT2R y)) < bpow Zaux.radix2 (femax t)).
{ intros. subst. 
  match goal with |- context [?A /\ ?B] =>
    assert A; [ |repeat split; auto  ]
  end.
  - revert HFINa. revert HFINfs. 
    set (u := (BPLUS t x y)).
    unfold BPLUS, BINOP. 
    destruct u; destruct a; simpl; intros; try discriminate; auto.
  - eapply is_finite_sum_no_overflow; try apply HFINs; auto. auto.
}
specialize (IHl s s0 s1 H4 H8 H12 Hinl H0); clear Hinl H0.
destruct IHl as (HFINs & IH).
match goal with |- context [?A /\ ?B] =>
  assert A; [ |repeat split; auto  ]
end.
{
unfold rounded, ov, FT2R in HOVfs.
pose proof (Binary.Bplus_correct (fprec t) (femax t) (fprec_gt_0 t) 
                      (fprec_lt_femax t) (plus_nan t)
                      BinarySingleNaN.mode_NE a s HFINa HFINs) as HCOR. 
apply Rlt_bool_true in HOVfs.
rewrite HOVfs in HCOR.
unfold BPLUS, BINOP; destruct HCOR as (_ & HFIN & _); auto.
}
pose proof (BPLUS_accurate t a HFINa s HFINs HOVfs) as Hplus.
destruct Hplus as (d' & e'& Hd'& He'& Hplus); rewrite Hplus; 
  clear Hplus HOVfs.
(* algebra *)
field_simplify_Rabs.
replace (- FT2R a * d' + s0 - FT2R s * d' - FT2R s - e') with
  ((s0 - FT2R s) - (FT2R s + FT2R a) * d' - e') by nra.
eapply Rle_trans; 
  [ apply Rabs_triang | eapply Rle_trans; [ apply Rplus_le_compat_r; apply Rabs_triang
    | rewrite !Rabs_Ropp] ].
eapply Rle_trans; 
  [apply Rplus_le_compat_r; apply Rplus_le_compat_r; apply IH | ].
eapply Rle_trans; 
  [apply Rplus_le_compat_r; apply Rplus_le_compat_l | ].
  rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
  eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat_r].
  assert (Hs: Rabs(FT2R s) <= error_rel t (length l) s1 + Rabs s1).
  { rewrite Rabs_minus_sym in IH; apply Rabs_le_minus in IH.
    eapply Rle_trans; [apply IH |apply Rplus_le_compat; try apply Rle_refl ].
    eapply sum_rel_R_Rabs. apply H8. apply H12.
  }
  apply Hs. apply Hd'.
eapply Rle_trans; 
  [apply Rplus_le_compat_l; apply He' | ].
cbv [error_rel]; rewrite !Zle_imp_le_bool.
set (D:= default_rel t).
set (E:= default_abs t).
replace ((length (a :: l) - 1)%nat) with (length l).
set (n:= length l). 
replace (Rabs (Rabs (FT2R a) + s1)) with (Rabs (FT2R a) + s1).
rewrite Rabs_pos_eq (*Rabs s1 = s1*). 
replace (((1 + D) ^ (n - 1) - 1) * (s1 + E / D) +
(((1 + D) ^ (n - 1) - 1) * (s1 + E / D) + s1 + Rabs (FT2R a)) * D + E) with
((1 + D) * ((1 + D) ^ (n - 1) - 1) * (s1 + E / D) + s1 * D + D * Rabs (FT2R a) + E) 
  by nra.
replace ((1 + D) * ((1 + D) ^ (n - 1) - 1) * (s1 + E / D) + s1 * D + D * Rabs (FT2R a) + E)
  with (D * Rabs (FT2R a) + ((1 + D) ^ n - 1 ) * (s1 + E / D)).
rewrite Rplus_assoc.
eapply Rle_trans; [  | rewrite Rmult_plus_distr_l ]. 
  apply Rle_refl.
apply Rplus_le_compat; try nra.
apply Rmult_le_compat; try apply Rabs_pos; try nra.
unfold D; apply Rlt_le; apply default_rel_gt_0.
rewrite Rcomplements.Rle_minus_r.
rewrite Rplus_comm.
replace (1 + D) with ((1 + D) ^ 1) at 1 by (simpl; nra).
apply Rle_pow.
rewrite Rplus_comm;
  apply Rcomplements.Rle_minus_l; field_simplify.
unfold D; apply Rlt_le; apply default_rel_gt_0.
(* (1 <= n)%nat *)
unfold n; apply length_not_empty_nat; auto.
symmetry.
rewrite Rmult_minus_distr_l.
rewrite Rmult_1_r.
replace ((1 + D) * (1 + D) ^ (n - 1)) with  ((1 + D) ^ n).
field_simplify; try nra; unfold D; try apply default_rel_sep_0.
replace (1 + D) with ((1 + D) ^ 1) at 2 by (simpl; nra).
  rewrite <- Rdef_pow_add.
  f_equal; rewrite plus_comm; rewrite Nat.sub_add; auto.
(* (1 <= n)%nat *)
unfold n; apply length_not_empty_nat; auto.
(* 0 <= s1 *)
eapply sum_rel_R_Rabs_pos; apply H12; auto.
symmetry.
rewrite Rabs_pos_eq (*Rabs s1 = s1*); try nra.
apply Rplus_le_le_0_compat; auto;
  try apply Rabs_pos.
(* 0 <= s1 *)
eapply sum_rel_R_Rabs_pos; apply H12; auto.
(* length l = (length (a :: l) - 1)%nat *)
simpl; lia.
(* (1 <= Z.of_nat (length (a :: l)))%Z *)
replace (length (a :: l)) with (length l +1)%nat by (simpl; lia).
rewrite Nat2Z.inj_add;
simpl; apply Z.le_sub_le_add_r;
ring_simplify.
replace 0%Z with (Z.of_nat 0)%Z by lia;
apply inj_le;
apply length_not_empty_nat'; auto.
(*(1 <= Z.of_nat (length l))%Z *)
replace 1%Z with (Z.of_nat 1) by lia;
apply inj_le;
apply length_not_empty_nat; auto.
Qed.

End NAN.