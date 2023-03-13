(*This file contains two theorems: forward and mixed error bounds for 
  the dot product of two floating point lists; the functional model for
  the vanilla dot product is defined in dotprod_model.v.*)

Require Import vcfloat.VCFloat vcfloat.IEEE754_extra.
Require Import List.
Import ListNotations.
Require Import common dotprod_model float_acc_lems op_defs list_lemmas.

Require Import Reals.
Open Scope R.


Section ForwardError. 
Context {NAN: Nans} {t : type}.

Variables (vF : list (ftype t * ftype t)).
Notation vR  := (map FR2 vF).
Notation vR' := (map Rabsp (map FR2 vF)).

Variable (fp : ftype t).
Hypothesis Hfp : dot_prod_rel vF fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

Variable (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel vR rp.
Hypothesis Hra : R_dot_prod_rel vR' rp_abs.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).

(* forward error bound *)
Lemma dotprod_forward_error:
  Rabs (FT2R fp - rp) <=  g (length vF) * Rabs rp_abs + g1 (length vF) (length vF - 1).
Proof.
revert Hfp Hrp Hra Hfin. revert fp rp rp_abs.
induction vF.
{
intros;
inversion Hrp;
inversion Hfp;
inversion Hra;
subst.
unfold g, g1; simpl;
rewrite Rminus_eq_0;
rewrite Rabs_R0;
field_simplify; try apply default_rel_sep_0;
  try apply Stdlib.Rdiv_pos_compat; try nra;
apply default_rel_gt_0.
}
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
{
subst; simpl.
rewrite (R_dot_prod_rel_single rp (FR2 a)); auto.
inversion Hfp. inversion H2. subst.
assert ( HFINa:
      (Binary.is_finite (fprec t) (femax t) (BMULT (fst a) (snd a)) = true /\
      Binary.is_finite (fprec t) (femax t) neg_zero = true)).
  { destruct (BMULT (fst a) (snd a)); unfold neg_zero; simpl; auto. }
  destruct HFINa as (A & C).
rewrite BPLUS_B2R_zero; auto.
pose proof BMULT_accurate'  (fst a) (snd a) A as Hmula.
destruct Hmula as (d' & e' & Hed' & Hd' & He' & B); rewrite B; clear B.
unfold g1, g; simpl.
inversion Hra. inversion H3; subst.
rewrite Rmult_1_r. rewrite !Rplus_0_r.
replace (1 + D - 1) with (D) by nra. field_simplify;
field_simplify_Rabs.  unfold FR2. destruct a; simpl.
eapply Rle_trans. apply Rabs_triang. rewrite Rabs_mult.
eapply Rle_trans.
apply Rplus_le_compat. apply Rmult_le_compat; try apply Rabs_pos.
apply Rle_refl. apply Hd'. apply He'.
rewrite Rmult_comm.
apply Rplus_le_compat; try nra.
rewrite <- Rabs_mult, Rabs_Rabsolu; try nra.
}
(* non-empty l *)
intros; inversion Hfp;
inversion Hrp; inversion Hra; subst.
(destruct (BPLUS_finite_e _ _ Hfin) as (A & B)).
(* IHl *)
specialize (IHl s s0 s1 H3 H7 H11 B).
destruct (BPLUS_accurate'  (BMULT (fst a) (snd a)) s Hfin) as (d' & Hd'& Hplus);
rewrite Hplus; clear Hplus.
destruct (BMULT_accurate'  (fst a) (snd a) A) as (d & e & Hed & Hd& He& Hmul); 
rewrite Hmul; clear Hmul.
(* algebra *)
apply length_not_empty_nat in H.
destruct a; cbv [ FR2 Rabsp fst snd].
simpl.
set (n:= length l) in *.
set (F:= FT2R f * FT2R f0).
field_simplify_Rabs.
replace (F * d * d' + F * d + F * d' + e * d' + e + FT2R s * d' + FT2R s - s0) with
((F * d * d' + F * d + F * d' + FT2R s * d') + (FT2R s - s0) + (1 + d') * e) by nra.
eapply Rle_trans;
  [ apply Rabs_triang | ].
eapply Rle_trans;
  [  apply Rplus_le_compat; [eapply Rle_trans;
  [ apply Rabs_triang | ] |]  | ].
apply Rplus_le_compat_l; apply IHl .
rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos | apply He].
rewrite  Rplus_assoc.
eapply Rle_trans;
  [  apply Rplus_le_compat_r ; eapply Rle_trans; [ apply Rabs_triang | ] | ].
apply Rplus_le_compat_l; rewrite Rabs_mult; rewrite Rmult_comm;
  apply Rmult_le_compat; [ apply Rabs_pos| apply Rabs_pos| apply Hd' | ].
{ apply Rabs_le_minus in IHl. assert (Hs: Rabs (FT2R s) <=
      g (length l) * Rabs s1 + g1 (length l) (length l - 1) + Rabs s1).
{ eapply Rle_trans. apply IHl. apply Rplus_le_compat_l.
apply (dot_prod_sum_rel_R_Rabs (map FR2 l)); auto. }
apply Hs. }
field_simplify.
fold D E n.
rewrite !Rplus_assoc. 
replace (Rabs (F * d * d' + (F * d + F * d')) +
(D * g n * Rabs s1 +
 (D * Rabs s1 +
  (D * g1 n (n - 1) +
   (Rabs s1 * g n + (g1 n (n - 1) + Rabs (1 + d') * E)))))) with
(Rabs (F * d * d' + (F * d + F * d')) + ((1+ D) * g n * Rabs s1 + D * Rabs s1) +
 (D * g1 n (n - 1) + (g1 n (n - 1) + Rabs (1 + d') * E))) by nra.
apply Rplus_le_compat.
replace (Rabs (Rabs (FT2R f) * Rabs (FT2R f0) + s1)) with
(Rabs ( FT2R f *  FT2R f0) +  Rabs s1).
rewrite !Rmult_plus_distr_l.
apply Rplus_le_compat.
eapply Rle_trans;
  [ apply Rabs_triang | ].
eapply Rle_trans;
  [ apply Rplus_le_compat; [rewrite !Rabs_mult| eapply Rle_trans; [apply Rabs_triang| ]] | ].
apply Rmult_le_compat; [rewrite <- Rabs_mult; apply Rabs_pos | apply Rabs_pos|  |  apply Hd'].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rplus_le_compat; rewrite Rabs_mult.
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd' ].
fold D F. replace (Rabs F * D * D + (Rabs F * D + Rabs F * D)) with
  ( ((1 + D)*(1+D) - 1) * Rabs F ) by nra.
apply Rmult_le_compat_r; try apply Rabs_pos; unfold D, g.
apply Rplus_le_compat; try nra.
rewrite <- tech_pow_Rmult.
apply Rmult_le_compat_l.
eapply Rle_trans with 1; try nra; apply default_rel_plus_1_ge_1.
eapply Rle_trans with ((1 + D)^1); try nra.
fold D; nra.
apply Rle_pow; auto with commonDB.
apply Req_le; rewrite one_plus_d_mul_g.
repeat f_equal;  try lia.
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) s1) at 2; auto.
symmetry.
rewrite Rabs_pos_eq; rewrite <-  Rabs_mult; auto. 
apply Rplus_le_le_0_compat; try apply Rabs_pos.
rewrite <- Rplus_assoc.
eapply Rle_trans; [apply Rplus_le_compat_l; 
  apply Rmult_le_compat_r; [ unfold E; apply default_abs_ge_0| eapply Rle_trans] | ].
apply Rabs_triang. rewrite Rabs_R1. 
apply  Rplus_le_compat_l; apply Hd'.
rewrite !Rmult_plus_distr_r. rewrite Rmult_1_l; unfold E.
rewrite <- !Rplus_assoc.
replace (D * g1 n (n - 1) + g1 n (n - 1)) with (g1 n (n-1) * (1+D)) by nra;
rewrite one_plus_d_mul_g1; auto.
rewrite Rplus_assoc; fold D E.
replace (E + D * E) with 
  ((1+D) * E) by nra.
eapply Rle_trans; [apply plus_d_e_g1_le; auto| apply Req_le; f_equal;lia].
Qed.

End ForwardError. 

Section MixedError. 
Context {NAN: Nans} {t : type}.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).

Variables (v1 v2 : list (ftype t)).
Hypothesis Hlen : length v1 = length v2.
Notation vF  := (combine v1 v2).

Variable (fp : ftype t).
Hypothesis Hfp : dot_prod_rel vF fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

(* mixed error bound *)
Lemma dotprod_mixed_error:
  exists (u : list R) (eta : R),
    length u = length v2 /\
    R_dot_prod_rel (combine u (map FT2R v2)) (FT2R fp - eta) /\
    (forall n, (n < length v2)%nat -> exists delta,
      nth n u 0 = FT2R (nth n v1 neg_zero) * (1 + delta) /\ Rabs delta <= g (length v2))  /\
    Rabs eta <= g1 (length v2) (length v2).
Proof.
revert Hfp Hfin Hlen. revert fp v1.
induction v2.
{ simpl; intros.   replace v1 with (@nil (ftype t)) in * by (symmetry; apply length_zero_iff_nil; auto). 
  exists [], 0; repeat split; 
  [inversion Hfp; subst; rewrite Rminus_0_r; simpl; auto;
  apply R_dot_prod_rel_nil  | | rewrite Rabs_R0; unfold g1, g; simpl; nra ]. 
  intros; exists 0; split; 
  [ assert (n = 0)%nat by lia; subst; simpl; nra | rewrite Rabs_R0; unfold g; nra].
}
intros.
  destruct v1; intros.
  { simpl in Hlen. pose proof Nat.neq_0_succ (length l); try contradiction. }
    assert (Hv1: l = [] \/ l <> []).
    destruct l; auto. right.
    eapply hd_error_some_nil; simpl; auto.
    assert (Hlen1: length l0 = length l) by (simpl in Hlen; auto).
    destruct Hv1.
    assert (l0 = []). { simpl in Hlen; apply length_zero_iff_nil;  
          apply length_zero_iff_nil in H; rewrite H in Hlen1; auto. }
    subst; clear Hlen1.
{ (* case singleton lists *)
clear IHl. inversion Hfp; subst. 
inversion H2; subst; clear H2.
 simpl in  Hfp, Hfin; unfold fst, snd.
assert (FINmul: Binary.is_finite (fprec t) (femax t) (BMULT f a) = true).
{ destruct (BMULT f a); unfold neg_zero in *; simpl; try discriminate; auto. }
rewrite BPLUS_B2R_zero in *; auto.
pose proof BMULT_accurate' f a FINmul as Hacc.
destruct Hacc as (d & e & Hed & Hd & He & Hacc).
exists [FT2R f * (1  +d)], e; repeat split.
{ simpl. rewrite Hacc. replace (FT2R f * FT2R a * (1 + d) + e - e) with
  (FT2R f * (1 + d) * FT2R a + 0) by (simpl; nra).
apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil. }
{ intros; exists d; split; auto. simpl in H. 
  destruct n. { simpl; auto. } 
  apply le_S_n in H; apply Nat.le_0_r in H; rewrite H; simpl; nra.
eapply Rle_trans; [apply Hd| apply d_le_g_1; simpl; auto].
}
eapply Rle_trans; [apply He|]. apply e_le_g1; simpl in *; auto.
} 
(* case cons lists*)
(* apply IH *)
pose proof (length_not_empty l H) as Hlen3.
inversion Hfp;  subst.
unfold fst, snd in Hfin, Hfp; unfold fst, snd.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
destruct (BMULT_finite_e _ _ A) as (C & _).
(* IHl *)
specialize (IHl s l0 H3 B Hlen1).
(* construct u *)
destruct (BPLUS_accurate' (BMULT f a) s Hfin) as (d' & Hd'& Hplus); 
rewrite Hplus; clear Hplus.
destruct (BMULT_accurate' f a A) as (d & e & Hed & Hd& He& Hmul); 
rewrite Hmul; clear Hmul.
destruct IHl as (u & eta & Hlenu & Hurel & Hun & Heta).
exists (FT2R f * (1+d) * (1 + d') :: map (Rmult (1+d')) u), 
  (e * (1 + d') + eta * (1 + d')).
repeat split.
{ simpl. rewrite map_length; auto. }
{ pose proof dot_prod_combine_map_Rmult (1+d') u (map FT2R l) (FT2R s - eta).
rewrite map_length in H0. specialize (H0 Hlenu Hurel); simpl.
replace
 ((FT2R f * FT2R a * (1 + d) + e + FT2R s) * (1 + d') -
   (e * (1 + d') + eta * (1 + d')))
with
 (FT2R f * (1 + d) * (1 + d') * FT2R a  + (FT2R s - eta) * (1 + d')) by nra.
apply R_dot_prod_rel_cons; rewrite Rmult_comm; auto. }
{ intros. destruct n. simpl.
{ simpl. exists ((1 + d) * (1 + d') -1); split.
  { field_simplify; nra. } 
  { field_simplify_Rabs. eapply Rle_trans; [apply Rabs_triang|].
    eapply Rle_trans; [apply Rplus_le_compat; [apply Rabs_triang | apply Hd' ] |].
    eapply Rle_trans; [apply Rplus_le_compat_r; apply Rplus_le_compat; [|apply Hd] |  ].
    rewrite Rabs_mult. apply Rmult_le_compat; 
        [apply Rabs_pos | apply Rabs_pos | apply Hd | apply Hd'].
    eapply Rle_trans with ((1 + D) * (1 + D) - 1); try nra.
    unfold g. apply Rplus_le_compat; try nra. 
    rewrite <- tech_pow_Rmult; apply Rmult_le_compat; try nra; try
    (eapply Rle_trans with 1; try nra; apply (default_rel_plus_1_ge_1)).
    eapply Rle_trans with ((1 + D) ^ 1); try nra.
    apply Rle_pow; try
    (eapply Rle_trans with 1; try nra; apply (default_rel_plus_1_ge_1)).
     rewrite <- Hlen1; auto. lia. }
}
simpl in H0; assert (Hn: (n < length l)%nat) by lia.
specialize (Hun n Hn);
   destruct Hun as (delta & Hun & Hdelta). simpl;
replace 0 with (Rmult  (1+d') 0) by nra. rewrite map_nth.
rewrite Hun.
exists ( (1+d') * (1+delta) -1).
split; [nra | ].
field_simplify_Rabs.
eapply Rle_trans; [apply Rabs_triang | ].
eapply Rle_trans; [apply Rplus_le_compat; [ apply Rabs_triang | apply Hdelta] | ].
eapply Rle_trans; [apply Rplus_le_compat_r; [rewrite Rabs_mult] | ].
apply Rplus_le_compat; [apply Rmult_le_compat;  try apply Rabs_pos | ].
apply Hd'.
apply Hdelta.
apply Hd'.
replace (D * g (length l) + D + g (length l)) with
((1 + D) * g (length l) *1 + D *1) by nra.
rewrite one_plus_d_mul_g.
rewrite Rmult_1_r.
apply Req_le; f_equal; lia.
}
simpl.
eapply Rle_trans; [apply Rabs_triang| ].
eapply Rle_trans; [apply Rplus_le_compat; [rewrite Rabs_mult| rewrite Rabs_mult] | ].
eapply Rmult_le_compat; try apply Rabs_pos.
apply He.
eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_R1; apply Rplus_le_compat_l; apply Hd'].
eapply Rmult_le_compat; try apply Rabs_pos.
apply Heta.
eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_R1; apply Rplus_le_compat_l; apply Hd'].
rewrite Rplus_comm. rewrite one_plus_d_mul_g1'.
assert (Hp: (1 <= S (length l))%nat) by lia.
pose proof @plus_d_e_g1_le' t (length l) (S (length l)) Hlen3 Hp as HYP; clear Hp.
eapply Rle_trans; [| apply HYP]; apply Req_le; nra.
Qed.

End MixedError.

Section ErrorExtra. 

Context {NAN: Nans} {t : type}.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).

Variables (v1 v2: list (ftype t)).
Hypothesis Hlen: length v1 = length v2.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) (dotprod t v1 v2) = true.

Lemma dotprod_mixed_error':
  exists (u : list R) (eta : R),
    length u = length v2 /\
    dotprodR u (map FT2R v2) = (FT2R (dotprod t v1 v2)) - eta /\
    (forall n, (n < length v2)%nat -> exists delta,
      nth n u 0 = FT2R (nth n v1 neg_zero) * (1 + delta) /\ Rabs delta <= g (length v2))  /\
    Rabs eta <= g1 (length v2) (length v2).
Proof.
intros.
assert (Datatypes.length (combine v1 v2) = length v1) by
 (rewrite combine_length; lia).
assert (Hlenr : length (rev v1) = length (rev v2)) by (rewrite !rev_length; auto).
rewrite <- rev_length in Hlen.
pose proof fdot_prod_rel_fold_right t v1 v2 as H1.
rewrite <- combine_rev in H1. 
rewrite rev_length in Hlen.
pose proof (dotprod_mixed_error (rev v1) (rev v2) Hlenr (dotprod t v1 v2) H1 Hfin) as 
  (u & eta & H2 & H3 & H4 & H5).
exists (rev u), eta; repeat split; auto.
rewrite rev_length in H2; rewrite <- rev_length in H2; auto.
pose proof dotprodR_rel u (map FT2R (rev v2)).
eapply R_dot_prod_rel_eq; eauto.
rewrite <- dotprodR_rev, <- map_rev; auto.
rewrite rev_length in H2; rewrite map_length; auto.
rewrite !rev_length in H4. 
intros. 
assert ((length u - S n < length v2)%nat).
{ rewrite rev_length in H2. 
rewrite H2. 
apply Nat.sub_lt; try lia.
}
specialize (H4 (length u - S n)%nat H6).
rewrite rev_nth in H4.
rewrite rev_nth.
destruct H4 as (delta & Hn & HD).
exists delta; split.
rewrite Hn; repeat f_equal.
rewrite rev_length in H2. 
rewrite Hlen.
rewrite H2. 
rewrite <- Nat.sub_succ_l.
simpl. lia.
apply Arith_prebase.lt_le_S_stt; auto.
apply HD.
rewrite rev_length in H2. 
rewrite H2; auto.
rewrite Hlen; auto.
rewrite !rev_length in H5; auto.
rewrite rev_length in Hlen; auto.
Qed.

End ErrorExtra.


Section SparseError. 
Context {NAN: Nans} {t : type}.

Variables (v1 : list (ftype t)).
Notation v1R := (map FT2R v1).

Notation Beq_dec_t := (@Beq_dec (fprec t) (femax t)).
Notation pos_zero := (Binary.B754_zero (fprec t) (femax t) false).
Definition nnz := (length v1 - @count_occ (ftype t) Beq_dec_t v1 pos_zero)%nat.

Lemma nnz_lemma : nnz = 0%nat -> forall x, In x v1 -> x = pos_zero.
Proof.
unfold nnz; 
induction v1;
try contradiction.
intros;
destruct H0.
{ subst. pose proof count_occ_unique Beq_dec_t pos_zero (x::l).
eapply (repeat_spec (length (x :: l))).
match goal with |- context [In x ?a] =>
replace a with (x::l)
end; simpl; auto.
apply H0. 
assert (0 + count_occ Beq_dec_t (x :: l) pos_zero  = length (x :: l))%nat.
{
rewrite <- H.
rewrite Nat.sub_add; try lia.
apply count_occ_bound.
}
simpl in H1.
simpl; auto.
}
apply IHl; auto.
assert (0 + count_occ Beq_dec_t (a :: l) pos_zero  = length (a :: l))%nat.
{
rewrite <- H.
rewrite Nat.sub_add; try lia.
apply count_occ_bound.
}
assert ( a::l = repeat pos_zero (length ((a::l)))).
eapply (count_occ_unique Beq_dec_t).
simpl in H1.
simpl; auto.
simpl in H2.
rewrite count_occ_cons_eq in H; auto.
inversion H2. auto.
Qed.

Lemma nnz_lemma_R : nnz = 0%nat -> forall x, In x v1R -> x = 0.
Proof.
intros H x Hin.
pose proof nnz_lemma H.
destruct (@Coqlib.list_in_map_inv (ftype t) R FT2R v1 x Hin) 
  as (x' & Hx' &Hx'').
specialize (H0 x' Hx'').
rewrite H0 in Hx'.
subst.
simpl; nra.
Qed.

Variables (v2 : list (ftype t)).
Hypothesis (Hlen : length v1 = length v2).
Variable (fp : ftype t).
Hypothesis Hfp : dot_prod_rel (combine v1 v2) fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

Lemma dot_prod_rel_nnz :
nnz = 0%nat -> FT2R fp = 0.
Proof.
intros.
pose proof nnz_lemma H.
revert H0 H Hfp Hlen Hfin. revert v2 fp.
induction v1; intros.
simpl in *; inversion Hfp; auto.
destruct v2; try discriminate; auto.
inversion Hfp; subst.
unfold fst, snd.
assert (Hin: forall x : ftype t, In x l -> x = pos_zero).
{ intros. apply H0; simpl; auto. }
assert (Hlen1:  length l = length l0) by (simpl; auto).
assert (HFIN: Binary.is_finite (fprec t) (femax t) s = true).
{ simpl in Hfin. destruct (BMULT a f); destruct s;
  destruct s0; try discriminate; simpl in *; auto; 
  destruct s; try discriminate; auto.
}
specialize (IHl l0 s Hin H H4 Hlen1 HFIN).
destruct (@BPLUS_accurate' t NAN (BMULT a f) s Hfin)
  as (d & _ & Hacc).
rewrite Hacc; clear Hacc.
rewrite IHl.
specialize (H0 a).
rewrite H0; [|simpl;auto].
destruct a; destruct f; simpl in *; try discriminate ; try nra.
Qed.

Variable (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel (map FR2 (combine v1 v2)) rp.
Hypothesis Hra : R_dot_prod_rel (map Rabsp (map FR2 (combine v1 v2))) rp_abs.

Lemma R_dot_prod_rel_nnz :
nnz = 0%nat -> rp = 0.
Proof.
intros H.
clear Hfin Hfp fp Hra rp_abs.
pose proof nnz_lemma_R H.
revert H0 H Hrp  Hlen. revert v2 rp.
induction v1; intros.
simpl in *; inversion Hrp; auto.
destruct v2; try discriminate; auto.
inversion Hrp; subst.
unfold FR2, fst, snd.
assert (Hin: forall x : R, In x (map FT2R l) -> x = 0).
{ intros. apply H0; simpl; auto. }
assert (Hlen1:  length l = length l0) by (simpl; auto).
specialize (IHl l0 s Hin H H4 Hlen1).
rewrite IHl.
specialize (H0 (FT2R a)).
rewrite H0; [|simpl;auto]; nra.
Qed.

Notation g := (@g t).
Notation g1 := (@g1 t).

Lemma nnz_cons1 a l :
a = pos_zero ->
(length (a :: l) - count_occ Beq_dec_t (a :: l) pos_zero = 
length l - count_occ Beq_dec_t l pos_zero)%nat.
Proof.
Admitted.

Lemma nnz_cons2 a l :
a <> pos_zero ->
(length (a :: l) - count_occ Beq_dec_t (a :: l) pos_zero = 
length (a :: l) - count_occ Beq_dec_t l pos_zero)%nat.
Proof.
Admitted.


Lemma sparse_dotprod_forward_error:
  Rabs (FT2R fp - rp) <=  g nnz * Rabs rp_abs + g1 nnz (nnz - 1).

Proof.
revert Hlen Hfp Hfin Hrp Hra.
revert rp rp_abs fp v2.
unfold nnz.
induction v1; intros.
{ simpl in Hlen; symmetry in Hlen; apply length_zero_iff_nil in Hlen; subst. 
inversion Hfp; inversion Hrp; subst; simpl; field_simplify_Rabs. 
  rewrite Rabs_R0. 
  apply Rplus_le_le_0_compat; auto with commonDB.
  apply Rmult_le_pos;  auto with commonDB.
  apply Rabs_pos. }
destruct v2; try discriminate.
inversion Hfp; inversion Hrp;  inversion Hra; subst.
unfold FR2, Rabsp, fst, snd. 
assert (Hlen1:  length l = length l0) by (simpl; auto).
assert (HFIN: Binary.is_finite (fprec t) (femax t) s = true).
{ simpl in Hfin. destruct (BMULT a f); destruct s;
   try discriminate; simpl in *; auto;
  destruct s; destruct s2; try discriminate; auto.
}
specialize (IHl s0 s1 s l0 Hlen1 H2 HFIN H6 H10). 
destruct (@BPLUS_accurate' t NAN (BMULT a f) s Hfin)
  as (d & _ & Hacc).
rewrite Hacc; clear Hacc.
assert (a = pos_zero \/ a <> pos_zero) by admit.
destruct H.
}
simpl.


induction nnz.
{ intros; rewrite H, H0; auto.
  field_simplify; field_simplify_Rabs.
  rewrite Rabs_R0. 
  apply Rplus_le_le_0_compat; auto with commonDB.
  apply Rmult_le_pos;  auto with commonDB.
  apply Rabs_pos. } 
clear H H0.
assert (n = 0%nat \/ (1 <= n)%nat) as Hn by lia; destruct Hn.

eapply Rle_trans. apply IHn.
subst. unfold g1, g. simpl; field_simplify;
  apply Rplus_le_le_0_compat; auto with commonDB;
  apply Rmult_le_pos;  auto with commonDB; apply Rabs_pos.
apply Rplus_le_compat.
apply Rmult_le_compat;  auto with commonDB. apply Rabs_pos.
apply Rle_refl.
eapply Rle_trans.
apply g1n_le_g1Sn; try lia. 
unfold g1, g.
repeat (rewrite Nat.sub_succ_l; try nra);
auto.
Admitted.

End SparseError.