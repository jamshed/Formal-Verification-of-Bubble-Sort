From VFA Require Import Perm.


Inductive sorted: list nat -> Prop := 
| sorted_nil:
    sorted nil
| sorted_1: forall x,
    sorted (x :: nil)
| sorted_cons: forall x y l,
   x <= y -> sorted (y :: l) -> sorted (x :: y :: l).


Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall al, Permutation al (f al) /\ sorted (f al).




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


Lemma bubble_sort_perm': forall n,
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



Lemma bubble_pass_empty_list: forall l,
    bubble_pass l = [] -> l = [].
Proof.
  intros l H. destruct l as [| h t] eqn:El.
  - reflexivity.
  - simpl in H. destruct (bubble_pass t) as [| h' t'] eqn:Ebpt.
    + inversion H.
    + bdestruct (h <=? h');
        inversion H.
Qed.


Lemma bubble_pass_min: forall l l' x y,
    bubble_pass l = (x :: l') -> In y l -> x <= y.
Proof.
  intro l. induction l as [| h t IHl']; intros l' x y Hbp Hin.
  - simpl in Hbp. inversion Hbp.
  - simpl in *. destruct (bubble_pass t) as [| h1 t1] eqn:Ebpt.
    + inversion Hbp. subst. clear Hbp.
      destruct Hin as [H | H].
      * omega.
      * apply bubble_pass_empty_list in Ebpt. subst. inversion H.
    + bdestruct (h <=? h1).
      * inversion Hbp. subst. clear Hbp.
        destruct Hin as [H' | H'].
        { omega. }
        { Check le_trans. apply le_trans with (m := h1).
          - apply H.
          - apply IHl' with (l' := t1).
            * reflexivity.
            * apply H'. }
      * inversion Hbp. subst. clear Hbp.
        destruct Hin as [H' | H'].
        { omega. }
        { apply IHl' with (l' := t1).
          - reflexivity.
          - apply H'. }
Qed.


Lemma bubble_pass_sorted: forall l l' x,
    bubble_pass l = (x :: l') ->
    sorted (bubble_sort' l' (length l')) ->
    sorted (x :: bubble_sort' l' (length l')).
Proof.
  intros l l' x Hbp Hs. 
  destruct l' as [| h' t'] eqn:El'.
  - simpl. apply sorted_1.
  - simpl in *. destruct (bubble_pass t') as [| h1 t1] eqn:Ebpt'.
    + apply bubble_pass_empty_list in Ebpt'. subst.
      simpl in *. apply sorted_cons.
      * Check bubble_pass_min. apply (bubble_pass_min l [h'] x h').
        { apply Hbp. }
        { assert (HP := bubble_pass_perm l). rewrite Hbp in HP.
          Check Permutation_in. apply Permutation_in with (l := [x; h']).
          - apply Permutation_sym. apply HP.
          - simpl. right. left. reflexivity. }
      * apply sorted_1.
    + bdestruct (h' <=? h1).
      * apply sorted_cons.
        { apply (bubble_pass_min l (h' :: t') x h').
          - apply Hbp.
          - Check bubble_pass_perm. assert (HP := bubble_pass_perm l).
            rewrite Hbp in HP. apply Permutation_in with ( l:= x :: h' :: t').
            + apply Permutation_sym. apply HP.
            + simpl. right. left. reflexivity. }
        { apply Hs. }
      * apply sorted_cons.
        { Check bubble_pass_min. apply (bubble_pass_min l (h' :: t') x h1).
          - apply Hbp.
          - apply Permutation_in with (l := x :: h' :: t').
            + rewrite <- Hbp. apply Permutation_sym. apply bubble_pass_perm.
            + simpl. right. right.
              apply Permutation_in with (l := bubble_pass t').
              * apply Permutation_sym. apply bubble_pass_perm.
              * rewrite Ebpt'. simpl. left. reflexivity. }
        { apply Hs. }
Qed.


Lemma bubble_pass_preserves_elems: forall l x,
    In x l <-> In x (bubble_pass l).
Proof.
  intros l x. split; intro H.
  - apply Permutation_in with (l := l).
    + apply bubble_pass_perm.
    + apply H.
  - apply Permutation_in with (l := bubble_pass l).
    + apply Permutation_sym. apply bubble_pass_perm.
    + apply H.
Qed.


Lemma bubble_sort'_sorted_aux: forall l x,
    sorted (bubble_sort' l (length l)) ->
    Forall (fun z => x <= z) l ->
    sorted (x :: bubble_sort' l (length l)).
Proof.
  intros l x Hs HF. rewrite Forall_forall in HF.
  destruct l as [| h t] eqn:El.
  - simpl. apply sorted_1.
  - simpl in *. destruct (bubble_pass t) as [| h1 t1] eqn:Ebpt.
    + apply sorted_cons.
      * apply HF. left. reflexivity.
      * apply bubble_pass_empty_list in Ebpt. subst.
        simpl. apply sorted_1.
    + bdestruct (h <=? h1).
      * apply sorted_cons.
        { apply HF. left. reflexivity. }
        { apply Hs. }
      * apply sorted_cons.
        { apply HF. right.
          apply bubble_pass_preserves_elems. rewrite Ebpt.
          left. reflexivity. }
        { apply Hs. }
Qed.


Lemma bubble_sort'_sorted: forall l n,
    length l = n -> sorted (bubble_sort' l n).
Proof.
  intros l n. generalize dependent l.
  induction n as [| n' IHn']; intros l H.
  - simpl. destruct l.
    + apply sorted_nil.
    + inversion H.
  - destruct l as [| h t] eqn:El.
    + inversion H.
    + simpl. destruct (bubble_pass t) as [| h1 t1] eqn:Ebpt.
      * apply bubble_pass_empty_list in Ebpt. subst. inversion H.
        simpl. apply sorted_1.
      * subst.
        assert (HP := bubble_pass_perm t). apply Permutation_length in HP.
        bdestruct (h <=? h1).
        { inversion H. subst.           
          rewrite Ebpt in HP. rewrite HP.
          Check bubble_sort'_sorted_aux. apply bubble_sort'_sorted_aux.
          - rewrite <- HP. apply IHn'. rewrite HP. reflexivity.
          - rewrite Forall_forall. intros x Hin. Check bubble_pass_min.
            apply le_trans with (m := h1).
            + apply H0.
            + apply (bubble_pass_min t t1 h1 x).
              * apply Ebpt.
              * apply bubble_pass_preserves_elems. rewrite Ebpt. apply Hin. }
        { inversion H. subst. rewrite Ebpt in HP.
          inversion HP. subst. assert (Hlen: length t = length (h :: t1)).
          { simpl. apply H2. }
          rewrite Hlen. apply bubble_sort'_sorted_aux.
          - rewrite <- Hlen. apply IHn'.
            symmetry. apply Hlen.
          - rewrite Forall_forall. intros x Hin.
            destruct Hin as [Hin | Hin].
            + omega.
            + Check bubble_pass_min. apply (bubble_pass_min t t1 h1 x).
              * apply Ebpt.
              * apply bubble_pass_preserves_elems.
                rewrite Ebpt. right. apply Hin. }
Qed.


Theorem bubble_sort_sorted: forall l,
    sorted (bubble_sort l).
Proof.
  intro l. unfold bubble_sort.
  apply bubble_sort'_sorted with (n := length l). reflexivity.
Qed.



Theorem bubble_sort_is_correct:
  is_a_sorting_algorithm bubble_sort.
Proof.
  unfold is_a_sorting_algorithm. intro l. split.
  - apply bubble_sort_perm.
  - apply bubble_sort_sorted.
Qed.
