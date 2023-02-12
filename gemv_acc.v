(*This file contains two main theorems: forward and mixed error bounds for 
  the fused muliply add dot product of two floating point lists; 
  the functional model for the fma dot product is defined in dotprod_model.v.*)

Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs dotprod_model sum_model.
Require Import dot_acc float_acc_lems list_lemmas gemv_defs.

Require Import Reals.
Open Scope R.

Section NAN.
Variable NAN: Nans.

(* mixed error bounds *)
Lemma mat_vec_mul_mixed_error:
  forall (t: type) (A: matrix) (v: vector)
  (Hfin: is_finite_vec (mvF A v))
  (Hlen: forall row, In row A -> length row = length v), (* row major form; each row equals length v *)
  exists (E : matrix) (eta : vector),
  map FT2R (mvF A v) = vec_sumR (mvR (mat_sumR (map_mat FT2R A) E) (map (@FT2R t) v)) eta /\ 
  (forall i j, (i < length E)%nat -> (j < length v)%nat -> 
  Rabs (matrix_index E i j 0%R) <= g t (length v) * Rabs (matrix_index (map_mat FT2R A) i j 0%R)) /\
  (forall k, In k eta -> Rabs k <= g1 t (length v) (length v)).
Proof.
intros ? ? ?.
induction A.
{ intros. exists (zero_matrix 0 0 0%R), []; repeat split.
 intros. simpl; rewrite matrix_index_nil.
 rewrite Rabs_R0; nra. 
 intros. simpl in H ; contradiction. }
intros; simpl.
assert (Hfin2 : is_finite_vec (mvF A v)).
{ unfold is_finite_vec in *; intros; apply Hfin; simpl; auto. }
assert (Hin2  : (forall row : list (ftype t), In row A -> length row = length v)).
{ intros; apply Hlen; simpl; auto. }
destruct (IHA Hfin2 Hin2) as (E & eta & IH1 & IH2 & IH3); clear IHA; rewrite IH1; clear IH1.
assert (Hlen': length a = length v).
{ apply Hlen; simpl; auto. }
assert (Hfin' : Binary.is_finite (fprec t) (femax t) (dotprod t a v) = true).
{ unfold is_finite_vec in *; apply Hfin; simpl; auto. }
destruct (dotprod_mixed_error' NAN t a v Hlen' Hfin') as (u & ueta & X & Y & Z1 & Z2).
set (A':= (map FT2R a :: map_mat FT2R A) : matrix).
assert (Ha: (length u = length (map FT2R a))).
{ rewrite X, map_length; auto. }
exists (vec_sum u (map FT2R a) Rminus :: E) , (ueta::eta); repeat split.
{
assert (FT2R (dotprod t a v) = dotprodR u (map FT2R v) + ueta) by nra.
rewrite H; clear H. simpl.
fold (vec_sum (map FT2R a) (vec_sum u (map FT2R a) Rminus) Rplus).
fold (vec_sumR (map FT2R a) (vec_sum u (map FT2R a) Rminus)).
replace (vec_sumR (map FT2R a) (vec_sum u (map FT2R a) Rminus)) with u.
rewrite vec_sumR_bounds; auto.
rewrite vec_sumR_opp; auto.
fold (vec_sumR u (map Ropp (map FT2R a))).
rewrite vec_sumR_comm.
rewrite vec_sumR_assoc.
rewrite vec_sumR_minus.
unfold vec_sumR.
symmetry.
replace (length (map FT2R a))  with (length u).
apply vec_sum_zeroR.
all: (repeat (try rewrite map_length;
try rewrite Hlen; auto; simpl; auto )).
apply vec_sum_length2; auto.
rewrite !map_length.
rewrite Hlen; auto; simpl; auto. }
destruct u.
{ rewrite map_length in Ha. subst A'.
simpl in Ha; symmetry in Ha; rewrite length_zero_iff_nil in Ha; 
subst; simpl; intros. 
destruct i; unfold matrix_index in *; 
destruct j; simpl; auto; 
[rewrite Rabs_R0; nra | rewrite Rabs_R0; nra | apply IH2; lia | apply IH2; lia ]. }
{ intros; simpl in Ha.
rewrite vec_sumR_opp.
destruct a; [simpl in Ha; try discriminate | ].
subst A'; simpl.
destruct (Z1 j H0) as (d & Hd1 & Hd2).
destruct i; unfold matrix_index; 
destruct j; simpl; auto.
{ simpl in Hd1; rewrite Hd1; field_simplify_Rabs. 
rewrite Rabs_mult, Rmult_comm; apply Rmult_le_compat; 
  [ apply Rabs_pos | apply Rabs_pos | apply Hd2 | apply Req_le; auto]. }
{ fold (map2 Rplus u (map Ropp (map FT2R a))).
fold (vec_sum u (map Ropp (map FT2R a)) Rplus).
fold (vec_sumR u (map Ropp (map FT2R a))).
unfold vec_sumR.
rewrite <- vec_sumR_opp; auto.
rewrite <- vec_sumR_nth; [| simpl in Ha; lia]; simpl in Hd1; rewrite Hd1.
replace (nth j (map FT2R a) 0) with 
 (nth j (map FT2R a) (@FT2R t neg_zero)) by f_equal.
rewrite map_nth; field_simplify_Rabs. 
rewrite Rabs_mult, Rmult_comm; apply Rmult_le_compat; 
  [ apply Rabs_pos | apply Rabs_pos | apply Hd2 | apply Req_le; auto]. }
{ unfold matrix_index in IH2; apply IH2; auto. simpl in H; lia. } 
{ unfold matrix_index in IH2; apply IH2; auto. simpl in H; lia. }  
simpl; auto. }
simpl; intros; destruct H; auto.
subst; apply Z2.
Qed.


End NAN.