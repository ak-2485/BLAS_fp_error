Require Import vcfloat.VCFloat.
Require Import List.

Require Import op_defs real_lemmas list_lemmas.

(* we use -0 in order to make use of the following property of fp arithmetic
  for finite x: (x + (-0) = x) *) 
Definition neg_zero {t: type} := Binary.B754_zero (fprec t) (femax t) true.

(* vanilla dot-product *)

Section NAN.
Variable NAN: Nans.

Definition dotprod {NAN: Nans} (t: type) (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BPLUS t (BMULT t (fst x12) (snd x12)) s) 
                (List.combine v1 v2) neg_zero.

Inductive dot_prod_rel {t : type} : 
            list (ftype t * ftype t) -> ftype t -> Prop :=
| dot_prod_rel_nil  : dot_prod_rel  nil (neg_zero )
| dot_prod_rel_cons : forall l (xy : ftype t * ftype t) s,
    dot_prod_rel  l s ->
    dot_prod_rel  (xy::l) (BPLUS t (BMULT t (fst xy) (snd xy)) s).

Lemma fdot_prod_rel_fold_right t :
forall (v1 v2: list (ftype t)), 
    dot_prod_rel (rev (List.combine v1 v2)) (dotprod t v1 v2).
Proof.
intros v1 v2. 
 unfold dotprod; rewrite <- fold_left_rev_right. 
induction (rev (List.combine v1 v2)).
{ simpl; auto. apply dot_prod_rel_nil. }
simpl. apply dot_prod_rel_cons. auto.
Qed.


(* FMA dot-product *)
Definition fma_dotprod {NAN: Nans} (t: type) (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BFMA (fst x12) (snd x12) s) 
                (List.combine v1 v2) neg_zero.

Inductive fma_dot_prod_rel {t : type} : 
            list (ftype t * ftype t) -> ftype t -> Prop :=
| fma_dot_prod_rel_nil  : fma_dot_prod_rel nil (neg_zero )
| fma_dot_prod_rel_cons : forall l (xy : ftype t * ftype t) s,
    fma_dot_prod_rel  l s ->
    fma_dot_prod_rel  (xy::l) (BFMA (fst xy) (snd xy) s).


Lemma fma_dot_prod_rel_fold_right t :
forall (v1 v2: list (ftype t)), 
    fma_dot_prod_rel (rev (List.combine v1 v2)) (fma_dotprod t v1 v2).
Proof.
intros v1 v2. 
 unfold fma_dotprod; rewrite <- fold_left_rev_right. 
induction (rev (List.combine v1 v2)).
{ simpl; auto. apply fma_dot_prod_rel_nil. }
simpl. apply fma_dot_prod_rel_cons. auto.
Qed.

End NAN.

(* real model *)

Inductive R_dot_prod_rel : 
            list (R * R) -> R -> Prop :=
| R_dot_prod_rel_nil  : R_dot_prod_rel  nil 0%R
| R_dot_prod_rel_cons : forall l xy s,
    R_dot_prod_rel  l s ->
    R_dot_prod_rel  (xy::l)  (fst xy * snd xy + s).

Definition sum: list R -> R := fold_right Rplus 0%R.

Lemma sum_rev l:
sum l = sum (rev l).
Proof.
unfold sum. 
rewrite fold_left_rev_right.
replace (fun x y : R => y + x) with Rplus
 by (do 2 (apply FunctionalExtensionality.functional_extensionality; intro); lra).
induction l; simpl; auto.
rewrite IHl.
rewrite <- fold_left_Rplus_0; f_equal; nra.
Qed.

Definition FR2 {t: type} (x12: ftype t * ftype t) := (FT2R (fst x12), FT2R (snd x12)).

Lemma R_dot_prod_rel_fold_right t :
forall (v1 v2: list (ftype t)) , 
   let prods := map (uncurry Rmult) (map FR2 (List.combine v1 v2)) in
    R_dot_prod_rel (rev (map FR2 (List.combine v1 v2))) (sum prods).
Proof.
intros. subst prods. rewrite sum_rev. rewrite <- !map_rev.
induction (map FR2 (rev (combine v1 v2))).
{ simpl. apply R_dot_prod_rel_nil. }
destruct a; simpl. apply R_dot_prod_rel_cons; auto.
Qed.

Definition Rabsp p : R * R := (Rabs (fst p), Rabs (snd p)).

Lemma R_dot_prod_rel_fold_right_Rabs t :
forall (v1 v2: list (ftype t)) , 
   let prods := map (uncurry Rmult) (map Rabsp (map FR2 (List.combine v1 v2))) in
    R_dot_prod_rel (rev (map Rabsp (map FR2 (List.combine v1 v2)))) (sum prods).
Proof.
intros. subst prods. rewrite sum_rev. rewrite <- !map_rev.
induction (map Rabsp (map FR2 (rev (combine v1 v2)))).
{ simpl. apply R_dot_prod_rel_nil. }
destruct a; simpl. apply R_dot_prod_rel_cons; auto.
Qed.

Import ListNotations.

Lemma R_dot_prod_rel_single rs a:
R_dot_prod_rel [a] rs -> rs = (fst a * snd a).
Proof.
intros.
inversion H.
inversion H3; subst; nra.
Qed.

Lemma R_dot_prod_rel_Rabs_eq :
forall l s,
R_dot_prod_rel (map Rabsp l) s -> Rabs s = s.
Proof.
induction  l.
{ intros.
inversion H.
rewrite Rabs_R0.
nra. }
intros.
inversion H; subst; clear H.
unfold Rabsp. destruct a; simpl.
replace (Rabs(Rabs r * Rabs r0 + s0)) with 
  (Rabs r * Rabs r0 + s0); try nra.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos;
apply Rabs_pos.
rewrite <- IHl; try apply Rabs_pos; auto.
Qed.


Lemma sum_rel_R_Rabs :
forall l s1 s2,
R_dot_prod_rel l s1 -> R_dot_prod_rel (map Rabsp l) s2 -> Rabs s1 <= Rabs s2.
Proof.
induction l.
{ intros.
inversion H.
inversion H0.
nra. }
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
unfold Rabsp; destruct a; simpl.
eapply Rle_trans; [
apply Rabs_triang |].
replace (Rabs (Rabs r * Rabs r0 + s0)) with 
  (Rabs r * Rabs r0 + s0).
eapply Rplus_le_compat; try nra.
rewrite Rabs_mult; nra.
rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos;
apply Rabs_pos.
rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
apply Rabs_pos.
Qed.



