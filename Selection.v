Require Export Coq.Lists.List.
From VFA Require Import Perm.


Fixpoint select (x: nat) (l: list nat): nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t => if x <=? h
              then let (j, l') := select x t in (j, h :: l')
              else let (j, l') := select h t in (j, x :: l')
  end.


(*
Fixpoint selsort l :=
  match l with
  | [] => []
  | h :: t => let (min, rem) := select h t
              in min :: selsort rem
  end.
 *)

Fixpoint selsort l n {struct n} :=
  match l, n with
  | h :: t, S n' => let (min, rem) := select h t
                    in min :: selsort rem n'
  | [], _ => []
  | _ :: _, O => []
  end.


Example out_of_gas: selsort [3; 1; 4; 1; 5] 3 <> [1; 1; 3; 4; 5].
Proof.
  simpl. unfold not. intro contra. inversion contra.
Qed.


Example too_much_gas: selsort [3; 1; 4; 1; 5] 10 = [1; 1; 3; 4; 5].
Proof.
  simpl. reflexivity.
Qed.


Definition selection_sort l := selsort l (length l).

Example sort_pi: selection_sort [3; 1; 4; 1; 5; 9; 2; 6; 5; 3; 5] = [1; 1; 2; 3; 3; 4; 5; 5; 5; 6; 9].
Proof.
  unfold selection_sort. simpl. reflexivity.
Qed.


Inductive sorted: list nat -> Prop :=
| sorted_nil: sorted []
| sorted_1: forall x, sorted [x]
| sorted_cons: forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).


Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall l, Permutation l (f l) /\ sorted (f l).



Definition selection_sort_correct: Prop :=
  is_a_sorting_algorithm selection_sort.


Lemma select_perm: forall x l,
    let (y, r) := select x l in
    Permutation (x :: l) (y :: r).
Proof.
  intros x l. generalize dependent x.
  induction l; intros; simpl in *.
  - apply Permutation_refl.
  - bdestruct (x <=? a).
    + specialize (IHl x). destruct (select x l).
      Search (Permutation (_ :: _ :: _) (_ :: _ :: _)).
      rewrite perm_swap. apply Permutation_sym. rewrite perm_swap.
      apply perm_skip. apply Permutation_sym. apply IHl.
    + specialize (IHl a). destruct (select a l).
      apply Permutation_sym. rewrite perm_swap.
      apply perm_skip. apply Permutation_sym. apply IHl.
Qed.


Lemma selsort_perm: forall n,
    forall l, length l = n -> Permutation l (selsort l n).
Proof.
  intros n.
  induction n; intros.
  - destruct l as [| h t] eqn:El.
    + simpl. apply perm_nil.
    + inversion H.
  - destruct l as [| h t] eqn:El; subst.
    + inversion H.
    + simpl. assert (HP := select_perm h t).
      destruct (select h t). apply Permutation_trans with (l' := n0 :: l).
      * apply HP.
      * Search (Permutation _ _ -> length _ = length _).
        apply Permutation_length in HP. simpl in HP. inversion HP.
        apply perm_skip. apply IHn. inversion H. subst.
        symmetry. apply H1.
Qed.


Theorem selection_sort_perm: forall l,
    Permutation l (selection_sort l).
Proof.
  intro l.
  apply selsort_perm. reflexivity.
Qed.



Lemma select_smallest_aux: forall x al y bl,
    Forall (fun z => y <= z) bl ->
    select x al = (y, bl) ->
    y <= x.
Proof.
  intros x al y bl HF Hs. assert (Hsp := select_perm x al).
  destruct (select x al). inversion Hs. subst.
  Search (Permutation _ _ -> In _ _ -> In _ _).
  apply Permutation_in with (x := x) in Hsp.
  - destruct Hsp.
    + omega.
    + Check Forall_forall. rewrite Forall_forall in HF.
      apply HF. apply H.
  - unfold In. left. reflexivity.
Qed.



Theorem select_smallest: forall x al y bl,
    select x al = (y, bl) -> Forall (fun z => y <= z) bl.
Proof.
  intros x al. generalize dependent x.
  induction al; intros; simpl in *.
  - inversion H. subst. Search (Forall _ []). apply Forall_nil.
  - bdestruct (x <=? a).
    + destruct (select x al) eqn:?H. inversion H. subst.
      Search (Forall _ (_ :: _)). apply Forall_cons. 
      * Check le_trans. apply le_trans with (m := x).
        { apply (select_smallest_aux x al y l).
          - apply IHal with (x := x). apply H1.
          - apply H1. }
        { apply H0. }
      * apply IHal with (x := x). apply H1.
    + destruct (select a al) eqn:?H. inversion H. subst.
      apply Forall_cons.
      * assert (Hs: y <= a).
        { apply (select_smallest_aux _ al _ l).
          - apply IHal with (x := a). apply H1.
          - apply H1. }
        { omega. }
      * apply IHal with (x := a). apply H1.
Qed.
