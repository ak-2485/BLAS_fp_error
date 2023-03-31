(*This file contains two main theorems: forward and mixed error bounds for 
  the fused muliply add dot product of two floating point lists; 
  the functional model for the fma dot product is defined in dotprod_model.v.*)

Require Import vcfloat.VCFloat.
Import ListNotations.
Require Import common op_defs dotprod_model sum_model.
Require Import dot_acc float_acc_lems list_lemmas gem_defs.
Require Import FEC.Matrix.ListMatrix.

From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.
From mathcomp.analysis Require Import Rstruct.
From mathcomp Require Import matrix all_ssreflect all_algebra ssralg ssrnum bigop.

Set Bullet Behavior "Strict Subproofs". 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import List ListNotations.


Notation "A *f v" := (mvF A v) (at level 40).
Notation "A *r v"  := (mvR A v) (at level 40).


Definition vec_to_mx {A: Type} v : list (list A) :=
  match v with 
  | [] => []
  | _ => v :: [] end.

Local Instance inhabitant_R : sublist.Inhabitant R.
apply R0. Defined.

Definition vector_to_vc (m' : nat) (v: @vector R) : 'cV[R]_m' := 
  let mx := vec_to_mx v in
  let m := Z.of_nat m' in 
\matrix_(i < m', j < 1) 
  (get mx (Z.of_nat (fintype.nat_of_ord i))(Z.of_nat (fintype.nat_of_ord j))).

Definition matrix_to_mx (m' n': nat) (mx: @gem_defs.matrix R) : 'M[R]_(m',n') := 
  let m := Z.of_nat m' in 
  let n := Z.of_nat n' in 
\matrix_(i < m', j < n') 
  (get mx (Z.of_nat (fintype.nat_of_ord i))(Z.of_nat (fintype.nat_of_ord j))).


Notation "A *fr v" := (vector_to_vc (length A) (map FT2R (mvF A v))) (at level 40).

Section MixedError. 
(* mixed error bounds *)
Context {NAN: Nans} {t : type}.

Lemma matrix_to_mx_nil n: 
matrix_to_mx 0 n [] = 0.
Proof.
  by rewrite /matrix_to_mx/get // /=;
   apply/matrixP =>  k i /[!mxE];
   rewrite !sublist.Znth_nil //.
Qed.

Lemma vector_to_vc_nil : 
vector_to_vc 0 [] = 0.
Proof.
  rewrite /vector_to_vc/vec_to_mx/get // /=;
   apply/matrixP =>  k i /[!mxE] /=;
   rewrite !sublist.Znth_nil //.
Qed.

Lemma fr_nil (A : @gem_defs.matrix  (ftype t)): 
 A *fr [] = 0.
Proof.
  rewrite /vector_to_vc/vec_to_mx/get/mvF/dotprod // /=.
  rewrite combine_nil.
Search combine nil.
   apply/matrixP =>  k i /[!mxE] /=.
   rewrite !sublist.Znth_nil //.




Lemma mvF_mulmx : forall (A : @gem_defs.matrix (ftype t)) v , 
  let A' := map_mat FT2R A in let v' := map FT2R v in
 (vector_to_vc (length A) (map FT2R (mvF A v)))= 
    (matrix_to_mx (length A) (length v) A') *m (vector_to_vc (length v) v').
Proof.
move => A v /=.
elim :v => /= //.
rewrite vector_to_vc_nil /mvF  /=.

rewrite /vector_to_vc /matrix_to_mx /get /vec_to_mx.
apply/matrixP =>  k i /[!mxE] /=.
elim :v => /= //.


elim: A => /= .
  rewrite vector_to_vc_nil matrix_to_mx_nil
    mul0mx //.
move => v' A IH .

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A: @gem_defs.matrix (ftype t)).
Variable (v: @gem_defs.vector (ftype t)).

Notation m := (length A).
Notation n := (length v).

Notation Ar := (matrix_to_mx m n (map_mat FT2R A)).
Notation vr := (vector_to_vc n (map FT2R v)).

Hypothesis Hfin : is_finite_vec (A *f v).
Hypothesis Hlen : forall x, In x A -> length x = n.

Notation " i '" :=
(fintype.nat_of_ord i) (at level 40).
 
From mathcomp.algebra_tactics Require Import ring.

Lemma mat_vec_mul_mixed_error:
  exists (E : 'M[R]_(m,n)) (eta : 'cV[R]_m),
    A *fr v =  (Ar + E) *m vr + eta 
    /\ (forall i j, (i ' < m)%nat -> (j ' < m)%nat -> 
      Rabs (E i j) <= g m * Rabs (Ar i j)) 
    /\ forall i, (i ' < m)%nat -> Rabs (eta i 0) <= g1 m m .
Proof.
revert Hfin Hlen. 
elim : A  => [{}Hfin _ | {} a m IHm Hfin Hlen ] /= .
exists (matrix_to_mx 0 n (zero_matrix 0 0 0%R)), 
  (vector_to_vc 0 []); repeat split => // /= .
  rewrite vector_to_vc_nil matrix_to_mx_nil 
      add0r addr0 mul0mx //.
 (* have Hn0: (0 <= n)%nat by lia.
  have: n = 0%nat \/ (0 < n)%nat by lia. 
move => [{}Hn0 | {} Hn0]. *)
have Hfin2 : is_finite_vec (m *f v). 
rewrite /is_finite_vec => x Hin; apply Hfin => /=; right => // . 
(*
{ unfold is_finite_vec in *. intros. apply Hfin; simpl; auto. }
assert (Hin2  : (forall row : list (ftype t), In row m -> length row = length v)).
{ intros; apply Hlen; simpl; auto. } *)
destruct (IHm Hfin2 ) as (E & eta & IH1 & IH2 & IH3) => [{}x H| {}].
  apply Hlen => /=; right => //.
have Hlen': length a = n by apply Hlen => /= ; left =>  //.
have Hfin': Binary.is_finite (fprec t) (femax t) (dotprod a v) = true by
  apply Hfin => /=; left => // . 
destruct (dotprod_mixed_error' a v Hlen' Hfin') as (u & ueta & X & Y & Z1 & Z2).
(*set (A':= (map FT2R a :: map_mat FT2R m) : gem_defs.matrix). *)
have Ha: (length u = length (map FT2R a)) by rewrite X map_length //.
set (y:= (vec_sum u (map FT2R a) Rminus :: E)).
exists (matrix_to_mx )
exists (vec_sum u (map FT2R a) Rminus :: E) , (ueta::eta); repeat split.
{
assert (FT2R (dotprod a v) = dotprodR u (map FT2R v) + ueta) by nra.
rewrite H; clear H. simpl. 
replace (map2 Rplus (map FT2R a) (u -v map FT2R a)) with u.
rewrite vec_sumR_bounds; auto.
symmetry; etransitivity; [ |apply  vec_sum_zeroR]. 
rewrite vec_sumR_opp, vec_sumR_comm; auto.
fold (vec_sumR u (map Ropp (map FT2R a))).
rewrite vec_sumR_assoc, vec_sumR_minus;
   try (unfold vec_sumR; rewrite Ha, !map_length; auto).
  rewrite !map_length; auto.
rewrite <- vec_sum_length; auto; rewrite map_length; auto.
}
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

End MixedError.

Section ForwardError.

(* forward error bounds *)
Context {NAN: Nans} {t : type}.

Variable (A : @gem_defs.matrix (ftype t)).
Variable (v: @gem_defs.vector (ftype t)).

Notation vr := (map FT2R v).
Notation Ar  := (map_mat FT2R A).

Hypothesis Hfin : is_finite_vec (A *f v).
Hypothesis Hlen : forall row, In row A -> length row = length v.

Definition vRabs v mu := 
  forall x, In x v -> Rabs x <= mu.

Notation "| A | <= u " := (vRabs A u) (at level 40). 

Notation m := (Z.of_nat (length A)).

Lemma forward_error :
   lvector_to_vec  m  (A *fr v)  = lvector_to_vec m (map FT2R v).
Proof.
destruct (mat_vec_mul_mixed_error A v Hfin Hlen) as (E & eta & HA & B & C).
rewrite HA.
unfold mvR.

Admitted.

End ForwardError.
