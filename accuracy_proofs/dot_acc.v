(*This file contains two theorems: forward and mixed error bounds for 
  the dot product of two floating point lists; the functional model for
  the vanilla dot product is defined in dotprod_model.v.*)

Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common float_acc_lems op_defs list_lemmas.
Require Import dotprod_model dot_acc_lemmas.

Require Import Reals.
Open Scope R.

Section MixedError. 
Context {NAN: Nans} {t : type}.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).

Variables (v1 v2: list (ftype t)).
Hypothesis Hlen: length v1 = length v2.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) (dotprodF v1 v2) = true.

Lemma dotprod_mixed_error:
  exists (u : list R) (eta : R),
    length u = length v2 /\
    dotprodR u (map FT2R v2) = (FT2R (dotprodF v1 v2)) - eta /\
    (forall n, (n < length v2)%nat -> exists delta,
      nth n u 0 = FT2R (nth n v1 neg_zero) * (1 + delta) /\ Rabs delta <= g (length v2))  /\
    Rabs eta <= g1 (length v2) (length v2).
Proof.
intros.
assert (Datatypes.length (combine v1 v2) = length v1) by
 (rewrite combine_length; lia).
assert (Hlenr : length (rev v1) = length (rev v2)) by (rewrite !rev_length; auto).
rewrite <- rev_length in Hlen.
pose proof dotprodF_rel_fold_right v1 v2 as H1.
rewrite <- combine_rev in H1. 
rewrite rev_length in Hlen.
pose proof (dotprod_mixed_error_rel (rev v1) (rev v2) Hlenr (dotprodF v1 v2) H1 Hfin) as 
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

End MixedError.

Section SparseError. 
Context {NAN: Nans} {t : type}.

Variables (v1 v2 : list (ftype t)).
Hypothesis (Hlen : length v1 = length v2).

Variable (fp : ftype t).
Hypothesis Hfp : dot_prod_rel (combine v1 v2) fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

Notation v1R := (map FT2R v1).

Variable (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel (map FR2 (combine v1 v2)) rp.
Hypothesis Hra : R_dot_prod_rel (map Rabsp (map FR2 (combine v1 v2))) rp_abs.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).
Notation nnzR := (nnzR v1R).

Lemma sparse_dotprod_forward_error:
  Rabs (FT2R fp - rp) <=  g nnzR * rp_abs + g1 nnzR (nnzR - 1).
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
 rewrite <- (R_dot_prod_rel_Rabs_eq [] rp_abs); auto;
  apply Rabs_pos. }
destruct v2; try discriminate.
assert (Hlen1 : length l = length l0) by (simpl; auto).
set (n2:= (common.nnzR (map FT2R l))%nat) in *.
inversion Hrp. inversion Hfp. inversion Hra; subst. 
assert (HFIN: Binary.is_finite (fprec t) (femax t) s0 = true).
{ simpl in Hfin. destruct (BMULT a f); destruct s0;
   try discriminate; simpl in *; auto;
  destruct s0; destruct s2; try discriminate; auto. }
assert (HFIN2: Binary.is_finite (fprec t) (femax t) (BMULT a f) = true).
{ simpl in Hfin. destruct (BMULT a f); destruct s0;
   try discriminate; simpl in *; auto. } simpl. 
specialize (IHl s s1 s0 l0 Hlen1 H6 HFIN H2 H10).
(* reason by cases on the head of the list *) 
destruct (Req_EM_T (FT2R a) 0%R). 
(* start  head of list is zero *)
{ rewrite e. unfold common.nnzR; rewrite nnz_cons.
replace (FT2R (BPLUS (BMULT a f) s0)) with (FT2R s0).
field_simplify_Rabs. 
eapply Rle_trans; [apply IHl|]. 
apply Req_le; f_equal; try nra. unfold n2, common.nnzR. 
rewrite Rabs_R0, Rmult_0_l,  Rplus_0_l; nra.
pose proof Bmult_0R a f HFIN2 as H; destruct H; auto; rewrite H;
try rewrite Bplus_neg_zero; try rewrite Bplus_neg_zero; auto;
repeat (destruct s0; simpl; auto). } (* end head of list is zero *) 
(* start head of list is non-zero *)
unfold common.nnzR, nnz. rewrite !count_occ_cons_neq; auto.
set (l1:= (map FT2R l)) in *.
set (n1:= (length (FT2R a :: l1) - @count_occ R Req_EM_T l1 0%R)%nat).
assert (n1 = S n2).
{ unfold n1, n2. pose proof @count_occ_bound R Req_EM_T 0%R l1.
  unfold common.nnzR, nnz.
  destruct (count_occ Req_EM_T l1 0%R); unfold l1 in *; simpl; try lia. }
(* start case on nnz = case on nnz in tail *)
assert (H0: (n2 = 0)%nat \/ (1<=n2)%nat) by lia; destruct H0. 
(* tail all zeros *)
{ rewrite H0 in *. rewrite H.
pose proof R_dot_prod_rel_nnzR l l0 Hlen1 s H2 H0; subst.
pose proof dot_prod_rel_nnzR l l0 Hlen1 s0 H6 HFIN H0.
pose proof R_dot_prod_rel_nnzR_abs l l0 Hlen1 s1 H10 H0; subst.
rewrite Bplus_0R; auto.
destruct (@BMULT_accurate' t NAN a f HFIN2)
  as (d' & e' & Hed' & Hd' & He' & Hacc).
rewrite Hacc; clear Hacc.
unfold g1, g.
simpl; field_simplify; 
field_simplify_Rabs. 
eapply  Rle_trans; [apply Rabs_triang | ].
apply Rplus_le_compat.
rewrite Rabs_mult.
rewrite Rmult_comm.
rewrite Rabs_mult. rewrite Rmult_assoc.
apply Rmult_le_compat_r; auto with commonDB.
rewrite <- Rabs_mult; apply  Rabs_pos.
eapply Rle_trans; [apply He'| ]; auto with commonDB; nra.
}
(* tail not all zeros *)
destruct (@BPLUS_accurate' t NAN (BMULT a f) s0 Hfin)
  as (d' & Hd' & Hacc).
rewrite Hacc; clear Hacc.
destruct (@BMULT_accurate' t NAN a f HFIN2)
  as (d & e & Hed & Hd & He & Hacc).
rewrite Hacc; clear Hacc. 
set (F:= FT2R a * FT2R f ).
field_simplify_Rabs.
replace (F * d * d' + F * d + F * d' + e * d' + e + FT2R s0 * d' + FT2R s0 - s) with
((F * d * d' + F * d + F * d' + FT2R s0 * d') + (FT2R s0 - s) + (1 + d') * e) by nra.
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
{ apply Rabs_le_minus in IHl. 
  assert (Hs: Rabs (FT2R s0) <=
        g n2 * s1 + g1 n2 (n2 - 1) + s1).
  { eapply Rle_trans. apply IHl. 
  apply Rplus_le_compat.
  apply Rplus_le_compat.
  apply Rmult_le_compat; auto with commonDB; try apply Rle_refl.
  rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (combine l l0)) s1); auto;
  apply Rabs_pos. 
  apply Rle_refl.
  rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (combine l l0)) s1); auto;
  apply (dot_prod_sum_rel_R_Rabs (map FR2 (combine l l0))); auto. }
apply Hs. }
field_simplify.
unfold g1, g in IHl. 
field_simplify in IHl.
set (D:= default_rel).
set (E:= default_abs).
rewrite !Rplus_assoc.
rewrite H.
match goal with |-context[?A<= ?B] =>
replace A with (Rabs (F * d * d' + (F * d + F * d')) + ((1+ D) * g n2 *  s1 + D *  s1) +
 (D * g1 n2 (n2 - 1) + (g1 n2 (n2 -1) + Rabs (1 + d') * E))) by nra;
replace B with 
(g (S n2) * Rabs F + s1 * g (S n2) + g1 (S n2) (S n2 - 1) ) by
(rewrite Rmult_assoc, <-Rabs_mult; fold F; nra)
end.
apply Rplus_le_compat.
apply Rplus_le_compat.
unfold g.
eapply Rle_trans;
  [ apply Rabs_triang | ].
eapply Rle_trans;
  [ apply Rplus_le_compat; [rewrite !Rabs_mult| eapply Rle_trans; [apply Rabs_triang| ]] | ].
apply Rmult_le_compat; [rewrite <- Rabs_mult; apply Rabs_pos | apply Rabs_pos|  |  apply Hd'].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rplus_le_compat; rewrite Rabs_mult.
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd' ].
fold D. replace (Rabs F * D * D + (Rabs F * D + Rabs F * D)) with
  ( ((1 + D)*(1+D) - 1) * Rabs F ) by nra.
apply Rmult_le_compat_r; try apply Rabs_pos; unfold D, g.
apply Rplus_le_compat; try nra.
rewrite <- tech_pow_Rmult.
apply Rmult_le_compat_l; auto with commonDB.
eapply Rle_trans with ((1 + D)^1); try nra.
fold D; nra.
apply Rle_pow; auto with commonDB. 
apply Req_le. unfold D,E. rewrite one_plus_d_mul_g.
rewrite Rmult_comm.
repeat f_equal;  try lia.
rewrite <- !Rplus_assoc.
replace (D * g1 n2 (n2 - 1) + g1 n2 (n2 - 1)) with (g1 n2 (n2-1) * (1+D)) by nra.
unfold D.
rewrite one_plus_d_mul_g1; auto.
eapply Rle_trans; [apply Rplus_le_compat_l |].
apply Rmult_le_compat_r; unfold E; auto with commonDB.
assert (Rabs (1 + d') <= 1 + D).
eapply Rle_trans; [apply Rabs_triang| rewrite Rabs_R1].
apply Rplus_le_compat_l; apply Hd'.
apply H1.
eapply Rle_trans; [apply plus_d_e_g1_le; auto| apply Req_le; f_equal;lia].
Qed.

End SparseError.
