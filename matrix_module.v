
(*From mathcomp Require Import all_ssreflect bigop all_algebra.
From mathcomp Require Import ssralg ssrnum ssrint ssrnum finmap matrix mxalgebra.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import cardinality set_interval mathcomp_extra.
From mathcomp.analysis Require Import  reals normedtype Rstruct.
From mathcomp.analysis Require Import sequences functions set_interval mathcomp_extra.
From mathcomp.analysis Require Import ereal signed topology normedtype prodnormedzmodule.
From mathcomp.analysis Require Import classical_sets.*)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval mathcomp_extra.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule normedtype sequences.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.



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

Variables (R: realType) (m n : nat).

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

End Inverse.

Section Maps.
Variables (m n : nat).
Variables (R: realType) (T: topologicalType).
Variable  (M: 'M[T]_(m.+1,m.+1)).

(* contractive maps are defd in sequences file*)
Definition f_app (f : 'rV[R]_m -> 'rV[R]_m)
        (u: 'rV[R]_m)  := fun n => iter n f u.

Goal forall (f : 'rV[R]_m -> 'rV[R]_m) (u: 'rV[R]_m) ,
       f_app f u 1 = f u.
rewrite/f_app/iter //. Qed.

Goal forall (f : 'rV[R]_m -> 'rV[R]_m) (u: 'rV[R]_m) ,
       f_app f u 0 =  u.
rewrite/f_app/iter //. Qed.



Variable  (R0 : realFieldType) (AM: set (matrix R m.+1 1)) .
Variable (AM1: set 'M[R]_(m.+1)) .
Variable (AV : set 'cV[R]_(m.+1)).

Canonical mat_R_CompleteNormedModule (a b : nat) :=
  [completeNormedModType R of (matrix R a.+1 b.+1)].

Import topology.numFieldTopology.Exports.
Import CompleteNormedModule.Exports.

From elpi Require Import elpi.

From HB Require Import structures.


(* A1 and AR work for statement, AV does not*)
Theorem Ban : forall (f : {fun AV >-> AV}) ,
is_contraction f -> closed AV ->
        exists2 x, AV x & x = f x .
Proof.
intros.
 apply banach_fixed_point.
Admitted.

Locate closed.
Print closed.

Print bounded_closed_compact.

Lemma bounded_closed_compact (R0 : realType) p (A1: set 'rV[R0]_p.+1) :
  bounded_set A1 -> closed A1 -> compact A1.


Theorem Ban
(R1 : realType) n (A1 : set 'rV[R1]_n.+1)
 : forall (f : {fun A1 >-> A1}) ,
is_contraction f -> closed A1 ->
        exists2 x, A x & x = f x .
Proof.

Variable (K: numDomainType).
Variable U : set 'rV[T]_m.
Variable f : {fun A >-> A}.

Goal f U = f U.

Goal is_contraction f.



Search nbhs matrix.
Definition mat_nbhs := nbhs M.
Print nbhs.


(* definition of the matrix condition number *)
Definition kappa (A : 'M[R]_m.+1) := `|(invmx A)| * `|A|.

Lemma Neumann_bound' (A : 'M[R]_m.+1):
        (1 - A) * \sum_(0 <= i < n.+1) A^i.
Proof.

Lemma Neumann_bound (F : 'M[R]_m.+1):
        `|invmx(1 - F)| <=  \sum_(0 <= i < n.+1) `|F|^i.
Proof.
unfold norm.



