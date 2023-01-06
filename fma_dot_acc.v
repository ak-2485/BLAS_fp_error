Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs dotprod_model float_acc_lems list_lemmas real_lemmas.

Require Import Reals.
Open Scope R.


Definition g (t: type) (n: nat) : R := ((1 + (default_rel t )) ^ n - 1).


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

Lemma g_pos t n: 0<= g t n. Proof. unfold g. induction n.
simpl; nra. eapply Rle_trans; [apply IHn| apply Rplus_le_compat; try nra].
simpl. eapply Rle_trans with (1 * (1+default_rel t)^n); try nra.
apply Rmult_le_compat; try nra. rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
field_simplify. apply default_rel_ge_0.
Qed.

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
destruct Hacc as (e & d & Hz & He & Hd & A). rewrite A; clear A.
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
destruct Hplus as (d' & e'& Hz & Hd'& He'& Hplus); rewrite Hplus; 
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

Definition g1 (t: type) (n: nat) : R := 
  INR n * default_abs t * (1 + g t n ).

Lemma g1_pos t n : 0 <= g1 t n.
Proof. unfold g1.
apply Rmult_le_pos; try apply pos_INR.
apply Rmult_le_pos; try apply pos_INR.
apply default_abs_ge_0. unfold g; field_simplify.
apply pow_le.
apply Fourier_util.Rle_zero_pos_plus1.
apply default_rel_ge_0. 
Qed.

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

Lemma dot_prod_combine_map_Rmult a u v r:
length u = length v ->
R_dot_prod_rel (combine u v) r -> 
R_dot_prod_rel (combine (map (Rmult a) u) v) (a * r). 
Proof. revert u r. induction v.
{ intros. rewrite !combine_nil in *.  
  inversion H0; subst; rewrite Rmult_0_r; apply R_dot_prod_rel_nil. }
destruct u.
  { intros; pose proof Nat.neq_0_succ (length v); try contradiction. }
  intros.   inversion H0. assert (Hlen: length u = length v) by (simpl in H; lia).
  specialize (IHv u s Hlen H4).
  simpl. replace (a * (r * a0 + s)) with 
    (a * r * a0 + a * s) by nra. apply R_dot_prod_rel_cons; auto.
Qed.

From Coquelicot Require Import Coquelicot.

Lemma one_plus_default_rel_ge t n:
1 <= (1 + default_rel t) ^ n.
Proof. induction n; simpl; auto; try nra.
eapply Rle_trans with (1 * 1); try nra.
apply Rmult_le_compat; try nra.
rewrite Rplus_comm. apply Rle_minus_l; field_simplify;
apply default_rel_ge_0.
Qed.


Lemma fma_dotprod_mixed_error: 
  forall (t: type) (v1 v2: list (ftype t)), 
  length v1 = length v2 -> 
  forall (fp : ftype t) (rp : R),
  fma_dot_prod_rel (List.combine v1 v2) fp -> 
  R_dot_prod_rel (map FR2 (List.combine v1 v2)) rp -> 
  (forall xy, In xy (List.combine v1 v2) ->   
      Binary.is_finite _ _ (fst xy) = true /\ Binary.is_finite _ _ (snd xy) = true) ->   
  Binary.is_finite (fprec t) (femax t) fp = true ->
  exists (u : list R) (eta : R), 
    length u = length v2 /\
    R_dot_prod_rel (List.combine u (map FT2R v2)) (FT2R fp - eta) /\ 
    (forall n, (n <= length v2)%nat -> exists delta, 
      nth n u 0 = FT2R (nth n v1 neg_zero) * (1 + delta) /\ Rabs delta <= g t (length v2))  /\
    Rabs eta <= g1 t (length v2). 
Proof.
intros t v1 v2 Hlen.
replace (combine (map Rabs (map FT2R v1))
     (map Rabs (map FT2R v2))) with (map Rabsp (map FR2 (combine v1 v2))) in *
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
revert Hlen. revert v1. induction v2.
{ intros. exists nil, 0. rewrite combine_nil in *. repeat split.
  inversion H; subst; rewrite Rminus_0_r; apply R_dot_prod_rel_nil.
  intros. exists 0; split. replace v1 with (@nil (ftype t)). 
        destruct n; simpl; nra. rewrite length_zero_iff_nil in Hlen; auto.
  simpl; simpl in H3; assert (n = 0)%nat by lia; subst; unfold g1, g; field_simplify; rewrite Rabs_R0; nra.
  unfold g1, g; simpl; rewrite Rabs_R0; nra. }
{ intros ? Hlen fp rp  Hfp Hrp Hin Hfin.
  destruct v1; intros.
  { pose proof Nat.neq_0_succ (length v2); try contradiction. }
  (* apply IH *)
  assert (HIN : (forall xy : ftype t * ftype t,
        In xy (combine v1 v2) ->
        Binary.is_finite (fprec t) (femax t) (fst xy) = true /\
        Binary.is_finite (fprec t) (femax t) (snd xy) = true)).
  { intros. assert (HIN: In xy (combine (f :: v1) (a :: v2))) by (simpl; auto);
    specialize (Hin xy HIN); auto. }  
  assert (length v1 = length v2) by (revert Hlen; simpl; lia).
  inversion Hfp; inversion Hrp; subst.
  assert (HFIN: Binary.is_finite (fprec t) (femax t) s = true).
  { revert Hfin; simpl. 
    assert (HIN' : In (f, a) (combine (f :: v1) (a :: v2))) by (simpl; auto). 
    specialize (Hin (f,a) HIN'). destruct Hin as (A & B). 
    destruct f, a, s; simpl; intros; try discriminate; auto. }
  specialize (IHv2 v1 H s s0 H3 H7 HIN HFIN).
  destruct IHv2 as (u  & eta & A & B & C & D ).
  (* construct u0 *)
assert (HFINaf:       
      Binary.is_finite (fprec t) (femax t) f = true /\
      Binary.is_finite (fprec t) (femax t) a = true).
  { intros. assert (HIN': In (f,a) (combine (f :: v1) (a :: v2))) by (simpl; auto);
    specialize (Hin (f,a) HIN'); simpl in Hin; auto. }  
    destruct HFINaf as (E & F).
    simpl in Hfin.
    assert (Hov: fma_no_overflow t (FT2R f) (FT2R a) (@FT2R t s)).
    { red; apply (is_finite_fma_no_overflow t (BFMA f a s)); auto. }
    pose proof fma_accurate t f E a F s HFIN Hov as HER.
    destruct HER as (d & e & Hz & Hd & He & HER). unfold fst, snd; rewrite HER.
    exists (FT2R f * (1+d) :: map (Rmult (1+d)) u), (e + eta * (1 + d)).
    repeat split. 
    { simpl. rewrite map_length; auto. } 
    { pose proof dot_prod_combine_map_Rmult (1+d) u (map FT2R v2) (FT2R s - eta).
      rewrite map_length in H0. specialize (H0 A B).
          replace  ((FT2R f * FT2R a + FT2R s) * (1 + d) + e - (e + eta * (1 + d))) with
         (FT2R f * (1 + d) * FT2R a + (FT2R s - eta)*(1+d)). simpl. 
          apply R_dot_prod_rel_cons. rewrite Rmult_comm; auto. 
          field_simplify; auto. }
    { intros. destruct n. simpl. exists d; split; auto.
unfold g. 
{ eapply Rle_trans. apply Hd. simpl.
set (x:= (default_rel t)). rewrite Rle_minus_r.
rewrite Rplus_comm. eapply Rle_trans with ((1+x) * 1); try nra.
eapply Rmult_le_compat; try nra. 
apply Fourier_util.Rle_zero_pos_plus1.
unfold x. apply default_rel_ge_0. 
subst x. apply one_plus_default_rel_ge.
}
assert (n<=length v2)%nat by (simpl in H0; lia); clear H0.
        specialize (C n H1); destruct C as (delta & C & HC). simpl.
simpl. replace 0 with (Rmult (1 + d) 0) by nra. rewrite map_nth.
rewrite C.
exists ( (1+d) * (1+delta) -1).
split; [nra | ]. 
field_simplify_Rabs.
eapply Rle_trans; [apply Rabs_triang | ].
eapply Rle_trans; [apply Rplus_le_compat; [ apply Rabs_triang | apply HC] | ].
eapply Rle_trans; [apply Rplus_le_compat_r; [rewrite Rabs_mult] | ].
apply Rplus_le_compat; [apply Rmult_le_compat;  try apply Rabs_pos | ].
apply Hd.
apply HC.
apply Hd.
unfold g.
set (x:= (1 + default_rel t) ^ length v2).
field_simplify.
replace (default_rel t * x + x - 1) with 
  (x * (1 + default_rel t) - 1) by nra.
simpl. fold x. apply Req_le; nra.
}
unfold g.
set (n:= length v2).
replace (INR (length (a :: v2))) with (INR n + 1)%R. simpl.
eapply Rle_trans. apply Rabs_triang.
eapply Rle_trans. apply Rplus_le_compat.
apply He. rewrite Rabs_mult. apply Rmult_le_compat;
try apply Rabs_pos. apply D.
apply Rabs_triang. 
eapply Rle_trans. apply Rplus_le_compat_l.

apply Rmult_le_compat_l. 
apply Rmult_le_pos; try apply pos_INR.
apply Rmult_le_pos; try apply pos_INR.
apply default_abs_ge_0.
apply Fourier_util.Rle_zero_pos_plus1.
apply g_pos.
apply Rplus_le_compat_l. apply Hd.
fold n.
rewrite Rabs_R1.
unfold g1, g. 
field_simplify. rewrite <- tech_pow_Rmult.
replace (INR (S n)) with (INR n +1) by (rewrite S_INR; auto).
field_simplify.
rewrite !Rplus_assoc.
apply Rplus_le_compat. apply Req_le; nra.
apply Rplus_le_compat. apply Req_le; nra.
replace (default_abs t * (1 + default_rel t) ^ n * default_rel t +
default_abs t * (1 + default_rel t) ^ n) with
(default_abs t * (1 + default_rel t) ^ n * (default_rel t + 1)) by nra.
eapply Rle_trans with (default_abs t * 1); try nra.
apply Rmult_le_compat; try nra. apply default_abs_ge_0.
eapply Rle_trans with (default_abs t * 1); try nra.
apply Rmult_le_compat; try nra. apply default_abs_ge_0.
apply one_plus_default_rel_ge.
pose proof one_plus_default_rel_ge t 1.
rewrite pow_1 in H0; rewrite Rplus_comm; auto.
unfold n. replace (length (a :: v2)) with (length v2 + 1)%nat. 
rewrite plus_INR; simpl; auto. simpl; lia.
}
Qed.


End NAN.

