
From HB Require Import structures.
From mathcomp Require Import all_ssreflect bigop all_algebra.
From mathcomp Require Import ssralg ssrnum ssrint ssrnum finmap matrix mxalgebra.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import cardinality set_interval mathcomp_extra.
From mathcomp.analysis Require Import ereal signed reals normedtype Rstruct.

Import Order.Theory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.

Local Open Scope ring_scope.

Section Examples.
Variables (R: realType) (m n : nat).

(* test examples of sharing using norm properties from ssrnum*)

Example matrix_triangle  (M N : 'M[R]_(m.+1, n.+1)) :
  `|M + N| <= `|M| + `|N|.
Proof.  apply ler_norm_add. Qed.

Example matrix_norm_positive (A : 'M[R]_(m.+1, n.+1)) : 
        0 <= `|A|.
Proof. apply normr_ge0. Qed.

End Examples.

Section Inverse.

Variables (R: realType) (K: unitRingType) (m n : nat).

Lemma ring_check (a1 a2 b : K):
        a1 = a2 -> a1 * b = a2 * b. 
Proof.
by move => H; rewrite H.
Qed.

Lemma ring_check2 : forall (a1 a2 b : K), 
        b \is a GRing.unit -> a1 * b = a2 * b -> a1 = a2. 
Proof.
move => a1 a2 b H1 H2. 
pose proof ring_check as H0.
specialize (H0 (a1 * b) (a2 * b) (b^-1) H2).
rewrite -!mulrA mulrV in H0 => [ | //].
by rewrite !mulr1 in H0.
Qed.

Lemma eqmx_mulr (b a1 a2: 'M[R]_m.+1) :
        a1 = a2 -> a1 * b = a2 * b. 
Proof.
by move => H; rewrite H.
Qed.

Lemma mulr_eqmx : forall  (b a1 a2: 'M[R]_m.+1) ,
        b \is a GRing.unit -> a1 *m b = a2 *m b -> a1 = a2. 
Proof.
move => b a1 a2  H1 H2. 
have : a1 * b * b^-1 = a2 * b * b^-1 by apply eqmx_mulr; apply H2.
rewrite -!mulrA mulrV // !mulr1 //. 
Qed.

Lemma invmx_mul (A B: 'M[R]_m.+1) :
        A \in unitmx -> B \in unitmx ->
        invmx (A *m B) = invmx B *m invmx A.
Proof.
move => H1 H2.
have H3: A *m B \in unitmx by (rewrite unitmx_mul; apply/andP => //=).
have H4: invmx (A *m B) * (A *m B) = invmx B *m invmx A * (A *m B).
 rewrite -mulmxE (mulVmx H3) mulmxE mulrA -mulmxE.
 rewrite -!mulmxA [invmx A *m (A *m B)]mulmxA (mulVmx H1) mul1mx (mulVmx H2) //.
apply (mulr_eqmx _ _ _ H3 H4).
Qed.


Lemma invmx_pert (A E: 'M[R]_m.+1) :
        A \in unitmx -> 1 + invmx A * E \in unitmx ->
        invmx (A + E) = invmx (1 + invmx A * E) * invmx A.
Proof.
move => H1 H2.
have H3: invmx (A + E) = invmx (A * (1 + invmx A * E)) by
rewrite mulrDr mulrA mulr1 -mulmxE (mulmxV H1) mul1mx //.
rewrite H3 (invmx_mul _ _ H1) //.
Qed.


