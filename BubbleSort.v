From VFA Require Import Perm.
From VFA Require Import Sort.



Fixpoint bubble_pass (l: list nat): list nat :=
  match l with
  | [] => []
  | h :: t => match (bubble_pass t) with
              | [] => [h]
              | h' :: t' => if h <=? h'
                            then h :: h' :: t'
                            else h' :: h :: t'
              end
  end.


Compute bubble_pass [1; 0; 5; 7; 4; 0; 3; 2].
Compute bubble_pass [].
Compute bubble_pass [9; 3; 2; 8; 7; 4; 5; 1; 0; 6].
Compute bubble_pass [4; 8; 0; 7; 2; 3; 1; 6; 5; 9].


Fixpoint bubble_sort' (l: list nat) (len: nat): list nat :=
  match len with
  | O => l
  | S len' => match (bubble_pass l) with
              | h :: t => h :: (bubble_sort' t len')
              | _ => []
              end
  end.


Definition bubble_sort (l: list nat): list nat :=
  bubble_sort' l (length l).


Compute bubble_sort [1; 0; 5; 7; 4; 0; 3; 2].
Compute bubble_sort [].
Compute bubble_sort [9; 3; 2; 8; 7; 4; 5; 1; 0; 6].
Compute bubble_sort [4; 8; 0; 7; 2; 3; 1; 6; 5; 9].



Lemma bubble_pass_perm: forall l, Permutation l (bubble_pass l).
Proof.
  intro l. induction l as [| h t IHl'].
  - simpl. Search (Permutation [] []). apply perm_nil.
  - simpl. destruct (bubble_pass t) as [| h' t'] eqn:Et.
    + simpl. Search (Permutation [] _). Search Permutation.
      apply Permutation_sym in IHl'. apply Permutation_nil in IHl'.
      subst. apply Permutation_refl.
    + bdestruct (h <=? h').
      * apply perm_skip. apply IHl'.
      * Search Permutation. apply Permutation_trans with (l' := h :: h' :: t').
        { apply perm_skip. apply IHl'. }
        { apply perm_swap. }
Qed.


Lemma bubble_sort_non_empty: forall n l,
    bubble_sort' l n = [] -> l = [].
Proof.
  intros. destruct l as [| h t] eqn:El.
  - reflexivity.
  - destruct n as [| n'] eqn:En.
    + simpl in H. inversion H.
    + simpl in H. destruct (bubble_pass t) as [| h' t'] eqn:Ebpt.
      * inversion H.
      * bdestruct (h <=? h');
          inversion H.
Qed.


Theorem bubble_sort_perm: forall n,
    forall l, length l = n -> Permutation l (bubble_sort' l n).
Proof.
  intros n. induction n; intros.
  - simpl. apply Permutation_refl.
  - destruct l as [| h t] eqn:El; subst.
    + inversion H.
    + simpl. assert (HBP := bubble_pass_perm t).
      destruct (bubble_pass t) eqn:Ebpt.
      * apply perm_skip. Search (Permutation [] _ -> _ = _).
        apply Permutation_sym in HBP. apply Permutation_nil in HBP.
        subst. inversion H. simpl. apply perm_nil.
      * bdestruct (h <=? n0).
        { apply perm_skip. eapply Permutation_trans.
          - apply HBP.
          - apply IHn. inversion H. subst.
            Search (Permutation _ _ -> length _ = length _).
            apply Permutation_length in HBP. symmetry. apply HBP. }
        { destruct (bubble_sort' (h :: l) n) eqn:Ebs.
          - apply bubble_sort_non_empty in Ebs. inversion Ebs.
          - apply Permutation_trans with (l' := h :: n0 :: l).
            + apply perm_skip. apply HBP.
            + rewrite perm_swap. apply perm_skip.
              rewrite <- Ebs. apply IHn.
              inversion H. apply Permutation_length in HBP.
              rewrite HBP. simpl. reflexivity.
        }
Qed.
