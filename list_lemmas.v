Require Import List Arith.
Import List ListNotations.


Lemma combine_map (A B : Type) (f : A -> B) g (v1 v2 : list A) :
(forall a a0, (f a, f a0) = g (a, a0)) -> 
combine (map f v1) (map f v2) = (map g (combine v1 v2)).
Proof. intros.
revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto.
Qed.

Lemma rev_empty (A: Type) : @rev A [] = []. simpl; auto. Qed.

Lemma combine_nil_r (A : Type) (l1 l2: list A) :
  length l1 = length l2 -> 
  combine l1 [] = combine l1 l2 -> l2 = [].
Proof. intros. 
rewrite combine_nil in H0. symmetry in H0.      
apply length_zero_iff_nil in H0.
      rewrite combine_length in H0.
  rewrite H in H0; clear H. rewrite Nat.min_id in H0. 
apply length_zero_iff_nil; auto.
Qed.

Lemma combine_nil_l (A : Type) (l1 l2: list A) :
  length l1 = length l2 -> 
  combine l1 [] = combine l1 l2 -> l1 = [].
Proof. intros. 
rewrite combine_nil in H0. symmetry in H0.      
apply length_zero_iff_nil in H0.
      rewrite combine_length in H0. symmetry in H.
  rewrite H in H0; clear H. rewrite Nat.min_id in H0. 
apply length_zero_iff_nil; auto.
Qed.

Lemma combine_app (A : Type) a1 a2 : forall (l1 l2 : list A),
  length l1 = length l2 -> combine l1 l2 ++ [(a1,a2)] = combine (l1 ++ [a1]) (l2 ++ [a2]).
Proof.
induction l1. 
{ intros. pose proof combine_nil_r A [] l2 H eq_refl; subst; simpl; auto. }
intros. destruct l2. 
{ pose proof combine_nil_l A (a :: l1) [] H eq_refl as H0; inversion H0. }
assert (Hlen: length l1 = length l2) by auto.
specialize (IHl1 l2 Hlen).
simpl; rewrite IHl1; simpl; auto.
Qed.

Lemma combine_rev (A : Type) (l1 l2: list A) :
length l1 = length l2 ->  
combine (rev l1) (rev l2) = rev (combine l1 l2).
Proof.
revert l1.
induction l2.
{ intros. rewrite !combine_nil; simpl; auto. }
intros. destruct l1.
{ simpl. auto. }
assert (Hlen: length l1 = length l2).
  simpl in H. auto.
specialize (IHl2 l1 Hlen).
simpl. rewrite <- IHl2.
rewrite <- combine_app; auto.
rewrite !rev_length; auto.
Qed.
