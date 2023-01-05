Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs dotprod_model float_acc_lems list_lemmas real_lemmas.

Require Import Reals.
Open Scope R.


Definition g (t: type) (n: nat) : R := ((1 + (default_rel t ))^n - 1).

Definition error_rel (t: type) (n: nat) (r : R) : R :=
  let e := default_abs t in
  let d := default_rel t in
  if (1 <=? Z.of_nat n) then 
    (g t (n-1)) * (Rabs r + e/d)
  else 0%R.


Section NAN.
Variable NAN: Nans.

(* forward error bounds *)

Lemma fma_dotprod_error': 
  forall (t: type) (v1 v2: list (ftype t)), 
  length v1 = length v2 -> forall fp rp rp_abs,
  let ov := bpow Zaux.radix2 (femax t) in
  fma_dot_prod_rel (List.combine v1 v2) fp -> 
  R_dot_prod_rel (List.combine (map FT2R v1) (map FT2R v2)) rp -> 
  R_dot_prod_rel (List.combine (map Rabs (map FT2R v1))  (map Rabs (map FT2R v2)) ) rp_abs ->
  (forall xy, In xy (List.combine v1 v2) ->   
      Binary.is_finite (fprec t) (femax t) (fst xy) = true /\ 
      Binary.is_finite _ _ (snd xy) = true) -> 
  Binary.is_finite (fprec t) (femax t) fp = true ->
  Rabs (FT2R fp - rp) <=  error_rel t (length v1 + 1) rp_abs.
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
subst;
unfold error_rel, g.
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
rewrite (R_dot_prod_rel_single rp (FR2 a)).
inversion Hfp. inversion H2. subst.
pose proof 
  is_finite_fma_no_overflow t (BFMA (fst a) (snd a) neg_zero) 
    (fst a) (snd a) neg_zero Hfin eq_refl as Hov.
assert ( HFINa: 
      (Binary.is_finite (fprec t) (femax t) (fst a) = true /\
      Binary.is_finite (fprec t) (femax t) (snd a) = true) /\
      Binary.is_finite (fprec t) (femax t) neg_zero = true).
  { split. apply Hin; simpl; auto. simpl; auto. } destruct HFINa as (A & C).
  destruct A as (A & B).
pose proof fma_accurate t (fst a) A (snd a) B neg_zero C Hov as Hacc; clear Hov A B C.
destruct Hacc as (e & d & He & Hd & A). rewrite A; clear A.
unfold error_rel, g; simpl.
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
clear Hin. destruct HFINa as (A & B).
assert (Hfins: Binary.is_finite (fprec t) (femax t) s = true).
{ subst; destruct a, s; destruct f; destruct f0; try discriminate; auto. }
specialize (IHl Hlen s s0 s1 H3 H7 H11 Hinl Hfins). 
assert (Hov: fma_no_overflow t (FT2R (fst a)) (FT2R (snd a)) (FT2R s)).
{ symmetry in H1. 
  pose proof is_finite_fma_no_overflow t fp (fst a) (snd a) s Hfin H1.
  red; auto.
}
pose proof (fma_accurate t (fst a) A (snd a) B s Hfins Hov) as Hplus.
destruct Hplus as (d' & e'& Hd'& He'& Hplus); rewrite Hplus; 
  clear Hplus Hov.
(* algebra *)
destruct a; cbv [ FR2 Rabsp fst snd].
field_simplify_Rabs.
replace (FT2R f * FT2R f0 * d' + FT2R s * d' + FT2R s + e' - s0) with
  ( (FT2R f * FT2R f0 + FT2R s) * d' + (FT2R s - s0) + e') by nra.
eapply Rle_trans; 
  [ apply Rabs_triang | eapply Rle_trans; [ apply Rplus_le_compat_r; apply Rabs_triang
    | ] ].
eapply Rle_trans; 
  [apply Rplus_le_compat_r; apply Rplus_le_compat_l; apply IHl | ].
eapply Rle_trans; 
  [apply Rplus_le_compat_r; apply Rplus_le_compat_r | ].
  rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
  eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat_l].
  assert (Hs: Rabs(FT2R s) <= error_rel t (length l + 1) s1 + Rabs s1).
  { apply Rabs_le_minus in IHl.
    eapply Rle_trans; [apply IHl |apply Rplus_le_compat; try apply Rle_refl ].
    eapply sum_rel_R_Rabs. apply H7. apply H11.
  }
  apply Hs. apply Hd'.
eapply Rle_trans; 
  [apply Rplus_le_compat_l; apply He' | ].
unfold error_rel, g; rewrite !Zle_imp_le_bool.
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


Lemma fma_dotprod_error: 
  forall (t: type)  (v1 v2: list (ftype t)), 
  length v1 = length v2 ->
  let prods := map (uncurry Rmult) (List.combine (map FT2R v1) (map FT2R v2)) in
  let abs_prods := map (uncurry Rmult) (List.combine (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))) in
  let ov := bpow Zaux.radix2 (femax t) in
  (forall xy, In xy (List.combine v1 v2) ->   
      Binary.is_finite _ _ (fst xy) = true /\ Binary.is_finite _ _ (snd xy) = true) ->
  Binary.is_finite _ _ (fma_dotprod t v1 v2) = true ->      
    Rabs (FT2R (fma_dotprod t v1 v2) - sum prods) <= error_rel t (length v1 + 1) (sum abs_prods).
Proof.
intros t v1 v2 Hlen. intros. 
assert (Datatypes.length (combine v1 v2) = length v1) by 
 (rewrite combine_length; lia).
assert (Hlenr : length (rev v1) = length (rev v2)) by (rewrite !rev_length; auto).
pose proof fma_dotprod_error' t (rev v1) (rev v2) Hlenr 
  (fma_dotprod t v1 v2) (sum prods) (sum abs_prods) as H2.
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

(* mixed error bounds *)

Definition g1 (t: type) (n: nat) (eta: R) (r : R) : R := 
  INR n * eta * (1  + g t n ).


Lemma FT2R_FR2 t : 
  (forall a a0 : ftype t, (FT2R a, FT2R a0) = FR2 (a, a0)) .
Proof. intros. unfold FR2; simpl; auto. Qed.

Lemma combine_single A v1 v2 (a : A * A) : 
  length v1 = length v2 -> 
  combine v1 v2 = [a] -> v1 = [fst a] /\ v2 = [snd a].
Proof.
intros. pose proof combine_split v1 v2 H.
rewrite H0 in H1. destruct a. 
simpl in H1. inversion H1; simpl; split; auto.
Qed.


Lemma fma_dotprod_mixed_error: 
  forall (t: type) (v1 v2: list (ftype t)), 
  length v1 = length v2 -> forall fp rp rp_abs,
  let ov := bpow Zaux.radix2 (femax t) in
  fma_dot_prod_rel (List.combine v1 v2) fp -> 
  R_dot_prod_rel (map FR2 (List.combine v1 v2)) rp -> 
  R_dot_prod_rel (List.combine (map Rabs (map FT2R v1))  (map Rabs (map FT2R v2)) ) rp_abs ->
  (forall xy, In xy (List.combine v1 v2) ->   
      Binary.is_finite _ _ (fst xy) = true /\ Binary.is_finite _ _ (snd xy) = true) ->   
  Binary.is_finite (fprec t) (femax t) fp = true ->
  exists (u : list (ftype t)) fp' eta,
    R_dot_prod_rel (map FR2 (List.combine u v2)) fp' /\ 
    (forall n, exists delta, FT2R (nth n u neg_zero) = FT2R (nth n v1 neg_zero) * (1 + delta) /\ 
    Rabs delta <= g t (length v1)) /\
    FT2R fp = fp' + eta /\
    Rabs eta <= INR (length v1) * default_abs t. 
Proof.
intros t v1 v2 Hlen.
replace (combine (map Rabs (map FT2R v1))
     (map Rabs (map FT2R v2))) with (map Rabsp (map FR2 (combine v1 v2))) in *
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
revert Hlen; induction v2.
{ intros. exists nil, 0, 0. rewrite combine_nil in *. repeat split.
  apply R_dot_prod_rel_nil.
  intros. exists 0; split. admit.
  rewrite Hlen. simpl. unfold g. field_simplify. rewrite Rabs_R0; nra.
  inversion H; simpl; nra.
  rewrite Hlen; simpl. rewrite Rabs_R0; nra. }
{ intros Hlen fp rp rp_abs ?  Hfp Hrp Hrpa Hin Hfin.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
{
subst; simpl. clear IHl. destruct a. admit.
}
 List.split.
replace (firstn (length [(f, f0)]) [(f, f0)]) with
  [(f,f0)] in Hc' by



Search firstn.
pose proof @firstn_all2 (ftype t)  (length [(f, f0)]) v2.
pose proof @firstn_all2 (ftype t)  (length [(f, f0)]) v1.
rewrite Hc in H, Hc', H0.
rewrite Hlen in Hc', H.
specialize (H (Nat.le_refl (length v2))).
specialize (H0 (Nat.le_refl (length v1))).

rewrite H in Hc'.
rewrite Hlen in H0.
rewrite H0 in Hc'.
pose proof combine_split v1 v2 Hlen as Hcs.
rewrite <- Hc' in Hcs.
simpl in Hcs.
inversion Hcs; subst.

inversion Hfp; subst. 
simpl in Hfp, Hfin.
inversion H4; subst.
assert (HFIN:       
      Binary.is_finite (fprec t) (femax t) f = true /\
      Binary.is_finite (fprec t) (femax t) f0 = true).
{ split; destruct f, f0; unfold neg_zero in Hfin; simpl in *;
  try discriminate; auto. }
destruct HFIN as (A & B).
assert (Hov: fma_no_overflow t (FT2R f) (FT2R f0) (@FT2R t neg_zero)).
{ red; fold ov; apply (is_finite_fma_no_overflow t (BFMA f f0 neg_zero)); auto. }
pose proof fma_accurate t f A f0 B neg_zero (neg_zero_is_finite t) Hov as HER.
destruct HER as (d & e & Hd & He & HER).
exists [FT2R f * (1 + d)], 
      (FT2R f * (1 + d) * FT2R f0),
     e; repeat split.
simpl.
apply R_dot_prod_rel_single'.
intros. exists d; split. admit.
unfold g, error_rel.
rewrite pow_1; field_simplify; auto.
revert HER; simpl; rewrite Rplus_0_r; intros.
rewrite HER; nra.
rewrite Rmult_1_l; auto.

(* [(f, f0)] = firstn (length [(f, f0)]) [(f, f0)] *)
pose proof @firstn_all2 (ftype t * ftype t) 
  (length [(f, f0)]) [(f, f0)] (Nat.le_refl (length [(f, f0)])).

}
inversion Hfp; subst. 
specialize (IHl Hlen).





rewrite Rabs_pos_eq; [apply Rle_refl| apply default_rel_ge_0].
inversion Hfp; subst.
inversion H4; subst.
simpl.
simpl in Hfp.


rewrite (R_dot_prod_rel_single rp (FR2 a)).
inversion Hfp. inversion H2. subst.
pose proof 
  is_finite_fma_no_overflow t (BFMA (fst a) (snd a) neg_zero) 
    (fst a) (snd a) neg_zero Hfin eq_refl as Hov.
assert ( HFINa: 
      (Binary.is_finite (fprec t) (femax t) (fst a) = true /\
      Binary.is_finite (fprec t) (femax t) (snd a) = true) /\
      Binary.is_finite (fprec t) (femax t) neg_zero = true).
  { split. apply Hin; simpl; auto. simpl; auto. } destruct HFINa as (A & C).
  destruct A as (A & B).
pose proof fma_accurate t (fst a) A (snd a) B neg_zero C Hov as Hacc; clear Hov A B C.
destruct Hacc as (e & d & He & Hd & A). rewrite A; clear A.
unfold g, error_rel; simpl.
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



Admitted.


End NAN.

