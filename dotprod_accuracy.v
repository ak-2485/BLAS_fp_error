Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import seqdotprod_model float_accuracy_lemmas op_defs.

Require Import Reals.
Open Scope R.

Definition error_rel (t: type) (n : nat) (r : R) : R :=
  let e := default_abs t in
  let d := default_rel t in
  if (1 <=? Z.of_nat n) then 
    ((1 + d)^(n-1) - 1) * (Rabs r + e/d)
  else 0%R.


Lemma dotprod_error': 
  forall (t: type) (v1 v2: list (ftype t)), 
  length v1 = length v2 -> forall fp rp rp_abs,
  let ov := bpow Zaux.radix2 (femax t) in
  fma_dot_prod_rel (List.combine v1 v2) fp -> 
    R_dot_prod_rel (List.combine (map FT2R v1) (map FT2R v2)) rp -> 
  R_dot_prod_rel (List.combine (map Rabs (map FT2R v1))  (map Rabs (map FT2R v2)) ) rp_abs ->
  (forall xy, In xy (List.combine v1 v2) ->   
      Binary.is_finite _ _ (fst xy) = true /\ Binary.is_finite _ _ (snd xy) = true) ->
  (forall x y z, BFMA x y z = fp -> Binary.is_finite _ _ fp = true /\
      Rabs (rounded t (FT2R x * FT2R y + FT2R z)) < ov) ->      
  Binary.is_finite (fprec t) (femax t) fp = true /\
  Rabs (FT2R fp - rp) <=  error_rel t (length v1  + 1) rp_abs.
Proof.
intros t v1 v2 Hlen.
rewrite (combine_map _ _ FT2R FR2).
replace (combine (map Rabs (map FT2R v1))
     (map Rabs (map FT2R v2))) with (map Rabsp (map FR2 (combine v1 v2))) in *
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
assert (Datatypes.length (combine v1 v2) = length v1) by 
 (rewrite combine_length; lia).
rewrite <- H. clear H; revert Hlen.
induction (List.combine v1 v2).
{
intros Hlen fp rp rp_abs ? Hfp Hrp Hrpa Hin Hfin.
inversion Hrp.
inversion Hfp.
inversion Hrpa.
subst; split; [simpl; auto|].  
unfold error_rel.
rewrite Zaux.Zle_bool_true; try lia.
simpl.
rewrite Rminus_eq_0;
rewrite Rabs_R0;
field_simplify; try apply default_rel_sep_0;
  try apply Stdlib.Rdiv_pos_compat; try nra;
apply default_rel_gt_0.
}
intros Hlen fp rp rp_abs ? Hfp Hrp Hrpa Hin Hfin.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
{
subst; simpl.
assert (HFIN: Binary.is_finite (fprec t) (femax t) fp = true).
  { inversion Hfp. specialize (Hfin (fst a) (snd a) s H0);
      destruct Hfin as (A & B); subst; auto. }
split; auto.
rewrite (R_dot_prod_rel_single rp (FR2 a)).
inversion Hfp. inversion H2. subst.
pose proof 
  is_finite_fma_no_overflow t (BFMA (fst a) (snd a) neg_zero) 
    (fst a) (snd a) neg_zero HFIN eq_refl as Hov.
assert ( HFINa: 
      (Binary.is_finite (fprec t) (femax t) (fst a) = true /\
      Binary.is_finite (fprec t) (femax t) (snd a) = true) /\
      Binary.is_finite (fprec t) (femax t) neg_zero = true).
  { split. apply Hin; simpl; auto. simpl; auto. } destruct HFINa as (A & C).
  destruct A as (A & B).
pose proof fma_accurate t (fst a) A (snd a) B neg_zero C Hov as Hacc; clear Hov A B C.
destruct Hacc as (e & d & He & Hd & A). rewrite A; clear A.
unfold error_rel; simpl.
inversion Hrpa. inversion H3; subst.
rewrite Rmult_1_r. rewrite !Rplus_0_r.
replace (1 + default_rel t - 1) with (default_rel t) by nra.
field_simplify_Rabs. unfold FR2, Rabsp. destruct a; simpl.
eapply Rle_trans. apply Rabs_triang. rewrite Rabs_mult.
rewrite Rmult_plus_distr_l. rewrite Rmult_comm.
replace (Rabs (Rabs (FT2R f) * Rabs (FT2R f0))) with
  (Rabs (FT2R f) * Rabs (FT2R f0)).
apply Rplus_le_compat. 
  rewrite Rabs_mult. apply Rmult_le_compat; try apply Rle_refl;
  try apply Rabs_pos; auto; apply Rmult_le_pos; try apply Rabs_pos.
  field_simplify; auto; try apply default_rel_sep_0.
symmetry. rewrite Rabs_pos_eq; auto.
  apply Rmult_le_pos; try apply Rabs_pos.
unfold FR2 in *. simpl in Hrp; auto.
}
(* non-empty l *)
intros; inversion Hfp.
inversion Hrp. 
inversion Hrpa. 
clear H0 H2 H4 H6 H8 H10 l0 l1 l2 xy xy1 xy0. 
assert (HFINa: 
        Binary.is_finite (fprec t) (femax t) (fst a) = true /\
      Binary.is_finite (fprec t) (femax t) (snd a) = true) by (apply Hin; simpl; auto).
(* IHl *)
assert (Hinl:forall xy : ftype t * ftype t,
       In xy l ->
       Binary.is_finite (fprec t) (femax t) (fst xy) = true /\
       Binary.is_finite (fprec t) (femax t) (snd xy) = true).
{ intros; apply Hin; simpl; auto. }
clear Hin.
specialize (Hfin (fst a) (snd a) s H1).
destruct Hfin as (HFINfp & HOVfp).
assert (H0: forall x y z : ftype t,
       BFMA x y z = s ->
       Binary.is_finite (fprec t) (femax t) s = true /\
       Rabs (rounded t (FT2R x * FT2R y + FT2R z)) < ov).
{ intros. subst. 
  match goal with |- context [?A /\ ?B] =>
    assert A; [ |repeat split; auto  ]
  end.
  { revert HFINa. revert HFINfp. 
    set (u :=  (BFMA x y z)).
    unfold BFMA. destruct a; simpl. 
    destruct u; destruct f; destruct f0; simpl; intros; 
        destruct HFINa; try discriminate; auto. }
  eapply is_finite_fma_no_overflow; try apply H0; auto. 
}
specialize (IHl Hlen s s0 s1 H3 H7 H11 Hinl H0). 
destruct IHl as (HFINs & IH).
match goal with |- context [?A /\ ?B] =>
  assert A; [ |repeat split; auto  ]
end.
{
unfold rounded, ov, FT2R in HOVfp.
destruct HFINa as (A & B).
pose proof (Binary.Bfma_correct (fprec t) (femax t) (fprec_gt_0 t) 
                      (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE (fst a) (snd a) s A B HFINs) as HCOR. 
apply Rlt_bool_true in HOVfp.
simpl in HCOR, HOVfp.
rewrite HOVfp in HCOR.
unfold BFMA; destruct HCOR as (_ & HFIN & _); auto.
}
destruct HFINa as (A & B).
pose proof (fma_accurate t (fst a) A (snd a) B s HFINs HOVfp) as Hplus.
destruct Hplus as (d' & e'& Hd'& He'& Hplus); rewrite Hplus; 
  clear Hplus HOVfp.
(* algebra *)
destruct a; cbv [ FR2 Rabsp fst snd].
field_simplify_Rabs.
replace (FT2R f * FT2R f0 * d' + FT2R s * d' + FT2R s + e' - s0) with
  ( (FT2R f * FT2R f0 + FT2R s) * d' + (FT2R s - s0) + e') by nra.
eapply Rle_trans; 
  [ apply Rabs_triang | eapply Rle_trans; [ apply Rplus_le_compat_r; apply Rabs_triang
    | ] ].
eapply Rle_trans; 
  [apply Rplus_le_compat_r; apply Rplus_le_compat_l; apply IH | ].
eapply Rle_trans; 
  [apply Rplus_le_compat_r; apply Rplus_le_compat_r | ].
  rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
  eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat_l].
  assert (Hs: Rabs(FT2R s) <= error_rel t (length l + 1) s1 + Rabs s1).
  { apply Rabs_le_minus in IH.
    eapply Rle_trans; [apply IH |apply Rplus_le_compat; try apply Rle_refl ].
    eapply sum_rel_R_Rabs. apply H7. apply H11.
  }
  apply Hs. apply Hd'.
eapply Rle_trans; 
  [apply Rplus_le_compat_l; apply He' | ].
cbv [error_rel]; rewrite !Zle_imp_le_bool.
set (D:= default_rel t).
set (E:= default_abs t).
replace (length ((f, f0) :: l) + 1 - 1)%nat with (length l + 1)%nat by (simpl; lia).
replace (length l + 1 - 1)%nat with (length l)%nat by lia.
set (n:= length l). 
replace (Rabs (Rabs (FT2R f) * Rabs (FT2R f0) + s1)) with 
  (Rabs (FT2R f) * Rabs (FT2R f0) + s1).
replace (Rabs s1) with s1.  
rewrite <- Rabs_mult. 
set (F:= Rabs (FT2R f * FT2R f0)).
replace ((F + (((1 + D) ^ n - 1) * (s1 + E / D) + s1)) * D +
((1 + D) ^ n - 1) * (s1 + E / D) + E) with
((1 + D) * ((1 + D) ^ n - 1) * (s1 + E / D) + F * D + s1 * D + E) by nra.
replace ((1 + D) * ((1 + D) ^ n - 1) * (s1 + E / D) + F * D + s1 * D + E) with
(((1 + D) ^ (n + 1) - 1) * (s1 + E / D) + F * D).
rewrite Rplus_assoc.
eapply Rle_trans; [  | rewrite Rmult_plus_distr_l ]. 
  apply Rle_refl.
rewrite Rplus_comm.
apply Rplus_le_compat; try nra.
rewrite Rmult_comm.
apply Rmult_le_compat; try apply Rabs_pos; try nra.
unfold D; apply Rlt_le; apply default_rel_gt_0.
rewrite Rcomplements.Rle_minus_r.
rewrite Rplus_comm.
replace (1 + D) with ((1 + D) ^ 1) at 1 by (simpl; nra); try lia.
apply Rle_pow; try lia.
rewrite Rplus_comm;
  apply Rcomplements.Rle_minus_l; field_simplify.
unfold D; apply Rlt_le; apply default_rel_gt_0.
symmetry.
rewrite Rmult_minus_distr_l.
rewrite Rmult_1_r.
replace ((1 + D) * (1 + D) ^ n) with  ((1 + D) ^ (n+1)).
field_simplify; try nra; unfold D; try apply default_rel_sep_0.
replace (1 + D) with ((1 + D) ^ 1) at 2 by (simpl; nra).
  rewrite <- Rdef_pow_add.
  f_equal;  lia. 
(* s1 = Rabs s1 *) rewrite (R_dot_prod_rel_Rabs_eq (map FR2 l) ); auto.
symmetry. rewrite Rabs_pos_eq; auto.
apply Rplus_le_le_0_compat; auto;
  try apply Rabs_pos.
apply Rmult_le_pos; try apply Rabs_pos.
(* 0 <= s1 *)
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) ); try apply Rabs_pos; auto.
simpl; lia.
(* (1 <= Z.of_nat (length l + 1))%Z *)
rewrite Nat2Z.inj_add;
simpl; apply Z.le_sub_le_add_r;
ring_simplify.
replace 0%Z with (Z.of_nat 0)%Z by lia;
apply inj_le;
apply length_not_empty_nat'; auto.
try simpl; auto.
Qed.


Lemma dotprod_error: 
  forall (t: type)  (v1 v2: list (ftype t)), 
  length v1 = length v2 ->
  let prods := map (uncurry Rmult) (List.combine (map FT2R v1) (map FT2R v2)) in
  let abs_prods := map (uncurry Rmult) (List.combine (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))) in
  let ov := bpow Zaux.radix2 (femax t) in
  (forall xy, In xy (List.combine v1 v2) ->   
      Binary.is_finite _ _ (fst xy) = true /\ Binary.is_finite _ _ (snd xy) = true) ->
  (forall x y z, BFMA x y z = (dotprod t v1 v2) -> Binary.is_finite _ _ (dotprod t v1 v2) = true /\
      Rabs (rounded t (FT2R x * FT2R y + FT2R z)) < ov) ->      
  Binary.is_finite (fprec t) (femax t) (dotprod t v1 v2) = true /\
    Rabs (FT2R (dotprod t v1 v2) - sum prods) <= error_rel t (length v1 + 1) (sum abs_prods).
Proof.
intros t v1 v2 Hlen. intros. 
assert (Datatypes.length (combine v1 v2) = length v1) by 
 (rewrite combine_length; lia).
assert (Hlenr : length (rev v1) = length (rev v2)) by (rewrite !rev_length; auto).
pose proof dotprod_error' t (rev v1) (rev v2) Hlenr 
  (dotprod t v1 v2) (sum prods) (sum abs_prods) as H2.
rewrite rev_length in H2.
rewrite combine_rev in H2; auto.
apply H2; clear H2; auto.
{ apply (fma_dot_prod_rel_fold_right t v1 v2). }
{ rewrite !map_rev.
rewrite combine_rev.
subst prods.
rewrite (combine_map _ _ FT2R FR2); try simpl; auto.
pose proof R_dot_prod_rel_fold_right t v1 v2 as HRrel; simpl in HRrel; auto.
rewrite !map_length; auto. }
{ rewrite !map_rev.
rewrite combine_rev.
subst abs_prods.
rewrite (combine_map _ _ Rabs Rabsp); try simpl; auto.
rewrite (combine_map _ _ FT2R FR2); try simpl; auto.
pose proof R_dot_prod_rel_fold_right_Rabs t v1 v2 as HRrel; simpl in HRrel; auto. 
rewrite !map_length; auto. }
intros. apply in_rev in H2. specialize (H xy H2); auto.
Qed.


End NAN.

