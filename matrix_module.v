From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval mathcomp_extra.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule. 
From mathcomp Require Import normedtype sequences.

Import Order.Theory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.
Import normedtype.NbhsNorm.

Import topology.numFieldTopology.Exports.
Import CompleteNormedModule.Exports.

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

(** Notes: 
 contractive maps are defined in sequences *)
Variables (m n : nat) (R: realType).
Variables (Sv : set 'cV[R]_(m.+1)).

Definition f_app (f : 'rV[R]_m -> 'rV[R]_m)
        (u: 'rV[R]_m)  := fun n => iter n f u.

Goal forall (f : 'rV[R]_m -> 'rV[R]_m) (u: 'rV[R]_m) ,
       f_app f u 1 = f u.
rewrite/f_app/iter //. Qed.

Goal forall (f : 'rV[R]_m -> 'rV[R]_m) (u: 'rV[R]_m) ,
       f_app f u 0 =  u.
rewrite/f_app/iter //. Qed.

Canonical mat_R_CompleteNormedModule (m' n' : nat) :=
  [completeNormedModType R of (matrix R m'.+1 n'.+1)].

Lemma Banach_test : forall (f : {fun Sv >-> Sv}) ,
  is_contraction f -> closed Sv -> (Sv !=set0)%classic ->
        exists2 x:'cV_m.+1, Sv x & x = f x .
Proof.
move => f A B C; apply banach_fixed_point => //.
Qed.

Definition lin2_mx (f: 'cV[R]_n.+1 -> 'cV[R]_m.+1) : 'M[R]_(m.+1, n.+1) := 
   \matrix[lin1_mx_key]_(j, i) f (delta_mx i 0) j 0.

Definition lin2_mx' (f: {fun Sv >-> Sv}) : 'M[R]_(m.+1) := 
   \matrix[lin1_mx_key]_(j, i) f (delta_mx i 0) j 0.

Variable f : {linear 'cV[R]_n.+1 -> 'cV[R]_m.+1}.
Variable g : {linear 'rV[R]_m.+1 -> 'rV[R]_n.+1}.


Lemma mul_cV_lin2 (u : 'cV_n.+1): 
   lin2_mx f *m u = f u.
Proof.
by rewrite {2}[u]matrix_sum_delta linear_sum; apply/colP=> i;
rewrite mxE summxE; apply eq_bigr => j _; rewrite big_ord1 linearZ !mxE mulrC.
Qed.

Lemma mul_cV_lin2' (u : 'cV_n.+1): 
   lin2_mx f *m u = f u.
Proof.
by rewrite {2}[u]matrix_sum_delta linear_sum; apply/colP=> i;
rewrite mxE summxE; apply eq_bigr => j _; rewrite big_ord1 linearZ !mxE mulrC.
Qed.

Lemma trmxeq (m' n' : nat) (A B : 'M[R]_(m',n')) : A = B -> A^T = B^T.
Proof. by move => H; rewrite H. Qed.

Lemma trmx_mul_rV_lin1 u : (u *m lin1_mx g)^T = (g u)^T.
Proof. by apply trmxeq; apply mul_rV_lin1. Qed.

Lemma trmxZ a (A : 'M[R]_n) : (a *: A)^T = a *: (A^T).
Proof. by apply/matrixP => k i /[!mxE]. Qed.

Variable fs : {fun Sv >-> Sv}.

(*
Lemma contraction_fixpoint_unique {R2 : realDomainType}
    {X : normedModType R2} (U : set X) (fg : {fun U >-> U}) (x y : X) :
  is_contraction fg -> U x -> U y -> x = fg x -> y = fg y -> x = y.
Proof.
case => q [q1 ctrfq] Ux Uy fixx fixy; apply/subr0_eq/normr0_eq0/eqP.
have [->|xyneq] := eqVneq x y. first by rewrite subrr normr0.
have xypos : 0 < `|x - y| by rewrite normr_gt0 subr_eq0.
suff : `|x - y| <= q%:num * `|x - y| by rewrite ler_pmull // leNgt q1.
by rewrite [in leLHS]fixx [in leLHS]fixy; exact: (ctrfq (_, _)).
Qed. *)
(*
Lemma prime_above (m' : nat) : exists2 p : nat, (m' < p)%nat & prime p.
Proof.
have /pdivP[p pr_p p_dv_m1]: (1 < m'`! + 1)%nat.
by rewrite addn1 ltnS fact_gt0.
exists p => //. rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
case: (pdivP m1_gt1) => [p pr_p p_dv_m1].
apply: contraL p_dv_m1 => p_le_m.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // 
  gtnNdvd ?prime_gt1.*)

Context {X : completeNormedModType R} (U : set X).
Variables (fg : {fun U >-> U}).
Variables (q : {nonneg R}) (ctrf : contraction q fg) (base : X) (Ubase : U base).
Let C := `|fg base - base| / (1 - q%:num).
Let y := fun n => iter n fg base.

(*
Lemma bounded_locally (T : topologicalType)
    (R1 : numFieldType) (V : normedModType R1) (A : set T) (df : T -> V) :
  [bounded df x | x in A] -> [locally [bounded df x | x in A]].
Proof. move=> /sub_boundedr AB x Ax. apply: AB; apply: within_nbhsW. Qed.*)

Lemma mx_norm_is_klipschitz k: 
`|lin2_mx' fs| < k -> 
k.-lipschitz_Sv fs.
Proof.
move => H . 
rewrite/dominated_by.
pose proof sub_boundedr.
within_nbhsW
rewrite locallyP.
pose proof @within_nbhsW (matrix_topologicalType (m.+1) (m.+1) R).
Locate "`=>`".
ProperFilter
rewrite locally_of.


Search norm 


Lemma norm_lt_contraction: 
  `|lin2_mx' fs| < 1 -> is_contraction fs.
Proof.
move => H.
exists `|lin2_mx' fs|%:nng => // (* see signed.v; x%:nng explicitly casts x to {nonneg R} *).
unfold contraction; simpl.
split => [//|].
apply dominated_by1.
Search (dominated_by ).
About lipschitz_on.
have
unfold is_contraction, contraction.
nonneg
assert (`|lin2_mx' fs| : nonneg).
have H1:= matrix_norm_positive R m m (lin2_mx' fs).

(* definition of the matrix condition number *)
Definition kappa (A : 'M[R]_m.+1) := `|(invmx A)| * `|A|.

Lemma Neumann_bound' (A : 'M[R]_m.+1):
        (1 - A) * \sum_(0 <= i < n.+1) A^i.
Proof.

Lemma Neumann_bound (F : 'M[R]_m.+1):
        `|invmx(1 - F)| <=  \sum_(0 <= i < n.+1) `|F|^i.
Proof.
unfold norm.



