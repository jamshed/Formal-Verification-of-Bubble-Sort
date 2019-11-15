From VFA Require Import Perm.


Fixpoint insert (v: nat) (l: list nat): list nat :=
  match l with
  | [] => [v]
  | h :: t => if v <=? h
              then v :: l
              else h :: (insert v t)
  end.


Fixpoint sort (l: list nat): list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Compute (sort [5; 4; 7; 0; 1; 2; 3; 1; 8; 9]).


Example sort_pi: sort [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5] =
                 [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
Proof.
  simpl. reflexivity.
Qed.


Eval compute in insert 7 [1; 3; 4; 8; 12; 14; 18].



Inductive sorted: list nat -> Prop :=
| sorted_nil:
    sorted nil
| sorted_1: forall x,
    sorted (x :: nil)
| sorted_cons: forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).


Check length.
Check nth.

Definition sorted' (l: list nat): Prop :=
  forall i j, i < j < (length l) -> (nth i l 0) <= (nth j l 0).


Definition is_a_sorting_algorithm (f: list nat -> list nat): Prop :=
  forall l, Permutation l (f l) /\ sorted (f l).



Search Permutation.

Lemma insert_perm: forall x l, Permutation (x :: l) (insert x l).
Proof.
  intros. induction l as [| h t IHl'].
  - simpl. Check Permutation_refl. apply Permutation_refl.
  - simpl. bdestruct (x <=? h).
    + apply Permutation_refl.
    + Check perm_swap. eapply perm_trans.
      * apply perm_swap.
      * Search (Permutation (_ :: _) (_ :: _)). apply perm_skip.
        apply IHl'.
Qed.



Theorem sort_perm: forall l, Permutation l (sort l).
Proof.  
  intro. induction l as [| h t IHl'].
  - simpl. Search (Permutation [] []). apply perm_nil.
  - simpl. apply perm_trans with (l' := (h :: sort t)).
    + apply perm_skip. apply IHl'.
    + apply insert_perm.
Qed.


Lemma insert_sorted: forall a l,
    sorted l -> sorted (insert a l).
Proof.
  intros a l H. induction H.
  - simpl. apply sorted_1.
  - simpl. bdestruct (a <=? x);
             apply sorted_cons; try omega; try apply sorted_1.
  - simpl. bdestruct (a <=? x).
    + apply sorted_cons;
        try assumption; try apply sorted_cons; try assumption.
    + simpl in IHsorted.
      bdestruct (a <=? y);
        apply sorted_cons; try omega; try assumption.
Qed.



Theorem sort_sorted: forall l,
    sorted (sort l).
Proof.
  intro l. induction l as [| h t IHl'].
  - simpl. apply sorted_nil.
  - simpl. apply insert_sorted. apply IHl'.
Qed.


Theorem insertion_sort_correct:
  is_a_sorting_algorithm sort.
Proof.
  unfold is_a_sorting_algorithm. intro l. split.
  - apply sort_perm.
  - apply sort_sorted.
Qed.
