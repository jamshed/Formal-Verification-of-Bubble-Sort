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
    + Search (Permutation [] _). Search Permutation.
      apply Permutation_sym in IHl'. apply Permutation_nil in IHl'.
      subst. apply Permutation_refl.
    + bdestruct (h <=? h').
      * apply perm_skip. apply IHl'.
      * apply Permutation_sym. rewrite perm_swap.
        apply perm_skip. apply Permutation_sym. apply IHl'.
Qed.


Lemma bubble_sort_empty_list: forall n l,
    bubble_sort' l n = [] -> l = [].
Proof.
  intros n l H. destruct l as [| h t] eqn:El.
  - reflexivity.
  - destruct n as [| n'] eqn:En.
    + simpl in H. inversion H.
    + simpl in H. destruct (bubble_pass t) as [| h' t'] eqn:Ebpt.
      * inversion H.
      * bdestruct (h <=? h');
          inversion H.
Qed.


Theorem bubble_sort_perm': forall n,
    forall l, length l = n -> Permutation l (bubble_sort' l n).
Proof.
  intros n. induction n; intros l H.
  - (* n = 0 *)
    simpl. apply Permutation_refl.
  - (* n = S n' *)
    destruct l as [| h t] eqn:El; subst.
    + (* l = [] *)
      inversion H.
    + (* l = h :: t *)
      simpl. assert (HBP := bubble_pass_perm t).
      destruct (bubble_pass t) as [| h1 t1] eqn:Ebpt.
      * (* bubble_pass t = [] *)
        apply perm_skip. Search (Permutation [] _ -> _ = _).
        apply Permutation_sym in HBP. apply Permutation_nil in HBP.
        subst. inversion H. subst. simpl. apply perm_nil.
      * (* bubble_pass t = h1 :: t1 *)
        bdestruct (h <=? h1).
        { (* h <= h1 *)
          apply perm_skip. eapply Permutation_trans.
          - apply HBP.
          - apply IHn. inversion H. subst.
            Search (Permutation _ _ -> length _ = length _).
            apply Permutation_length. apply Permutation_sym. apply HBP. }
        { (* h > h1 *)
          destruct (bubble_sort' (h :: t1) n) as [| h2 t2] eqn:Ebs.
          - (* bubble_sort' (h :: t1) n = [] *)
            apply bubble_sort_empty_list in Ebs. inversion Ebs.
          - (* bubble_sort' (h :: t1) n = h2 :: t2 *)
            apply Permutation_trans with (l' := h :: h1 :: t1).
            + apply perm_skip. apply HBP.
            + rewrite perm_swap. apply perm_skip.
              rewrite <- Ebs. apply IHn.
              inversion H. subst.
              apply Permutation_length in HBP.
              rewrite HBP. simpl. reflexivity.
        }
Qed.


Theorem bubble_sort_perm: forall l,
    Permutation l (bubble_sort l).
Proof.
  intro l.
  apply bubble_sort_perm'. reflexivity.
Qed.

