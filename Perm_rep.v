Require Import Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Export ListNotations.
Require Export Permutation.


Check Nat.lt.
Check lt.
Goal Nat.lt = lt.
Proof. reflexivity. Qed.
Check Nat.ltb.
Locate "_ < _".
Locate "<?".

Check Nat.ltb_lt.

Locate "<=?".
Check le.
Check Nat.leb_le.

Check beq_nat.


Notation "a >=? b" := (Nat.leb b a)
                        (at level 70, only parsing): nat_scope.
Notation "a >? b" := (Nat.ltb b a)
                       (at level 70, only parsing): nat_scope.
Notation "a =? b" := (beq_nat a b)
                       (at level 70): nat_scope.


Print reflect.

Lemma beq_reflect: forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  Check iff_reflect. apply iff_reflect. symmetry.
  Check Nat.eqb_eq. apply Nat.eqb_eq.
Qed.

Lemma blt_reflect: forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.
  Check Nat.ltb_lt. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect: forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.
  Check Nat.leb_le. apply Nat.leb_le.
Qed.



Example reflect_example1: forall a, (if a <? 5 then a else 2) < 6.
Proof.
  intro a.
  Check blt_reflect. destruct (blt_reflect a 5) as [H | H].
  - omega.
  - Check not_lt. apply not_lt in H. omega.
Qed.



Hint Resolve blt_reflect ble_reflect beq_reflect: bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
                    evar (e: Prop);
                    assert (H: reflect e X); subst e;
                    [eauto with bdestruct
                    | destruct H as [H|H];
                      [ | try first [apply not_lt in H | apply not_le in H]]].


Example reflect_example2: forall a, (if a <? 5 then a else 2) < 6.
Proof.
  intros.
  bdestruct (a <? 5).
  - omega.
  - omega.
Qed.


Ltac inv H := inversion H; clear H; subst.




Module Exploration1.

  Theorem omega_example1:
    forall i j k,
      i < j ->
      ~(k - 3 <= j) ->
      k > i.
  Proof.
    intros.
    Search (~ _ <= _ -> _). apply not_le in H0.
    Search (_ > _ -> _ > _ -> _ > _). apply (gt_trans k j i).
    - apply (gt_trans k (k - 3) j).
  Abort.

  Theorem bogus_substraction: ~ (forall k, k > k - 3).
  Proof.
    intro.
    specialize (H O) as H0. simpl in H0. inversion H0.
  Qed.


  Theorem omega_example1: forall i j k,
        i < j ->
        ~(k - 3 <= j) ->
        k > i.
  Proof.
    intros.
    apply not_le in H0.
    unfold gt in H0. unfold gt.
    Search (_ < _ -> _ <= _ -> _ < _). apply (lt_le_trans i j k).
    - apply H.
    - Check le_trans. apply (le_trans j (k - 3) k).
      + Search (_ < _ -> _ <= _). apply lt_le_weak. apply H0.
      + Check le_minus. apply le_minus.
  Qed.


  Theorem omega_example2: forall i j k,
      i < j ->
      ~(k - 3 <= j) ->
      k > i.
  Proof.
    intros.
    omega.
  Qed.



  Definition maybe_swap (al: list nat): list nat :=
    match al with
    | a :: b :: ar => if a >? b then (b :: a :: ar) else al
    | _ => al
    end.

  Example maybe_swap123:
    maybe_swap [1; 2; 3] = [1; 2; 3].
  Proof.
    simpl. reflexivity.
  Qed.

  Example maybe_swap321:
    maybe_swap [3; 2; 1] = [2; 3; 1].
  Proof.
    simpl. reflexivity.
  Qed.


  Check (1 > 2).
  Check (1 >? 2).

  Locate ">?".

  Print Nat.ltb.

  Locate ">=?".

  Locate leb.
  Print leb.
  Print Nat.leb.


  Theorem maybe_swap_idempotent: forall al,
      maybe_swap (maybe_swap al) = maybe_swap al.
  Proof.
    intros. destruct al as [| h t].
    - simpl. reflexivity.
    - destruct t as [| h' t'].
      + simpl. reflexivity.
      + simpl. destruct (h' <? h) eqn:E.
        * simpl. destruct (h <? h') eqn:E'.
          try omega.
  Abort.


  Theorem maybe_swap_idempotent: forall l,
      maybe_swap (maybe_swap l) = maybe_swap l.
  Proof.
    intros. destruct l as [| h t] eqn:E.
    - simpl. reflexivity.
    - destruct t as [| h' t'] eqn:E'.
      + simpl. reflexivity.
      + simpl. bdestruct (h' <? h).
        * simpl. bdestruct (h <? h').
          { omega. }
          { reflexivity. }
        * simpl. bdestruct (h' <? h).
          { omega. }
          { reflexivity. }
  Qed.



  Theorem maybe_swap_idempotent': forall l,
      maybe_swap (maybe_swap l) = maybe_swap l.
  Proof.
    intro l. destruct l as [| h t] eqn:El.
    - simpl. reflexivity.
    - destruct t as [| h' t'] eqn:Et.
      + simpl. reflexivity.
      + simpl. bdestruct (h' <? h).
        * simpl. bdestruct (h <? h').
          { omega. }
          { reflexivity. }
        * simpl. bdestruct (h' <? h).
          { omega. }
          { reflexivity. }
  Qed.




  Locate Permutation.
  Check Permutation.
  Print Permutation.
  Search Permutation.


  Example butterfly: forall b u t e r f l y: nat,
      Permutation ([b; u; t; t; e; r] ++ [f; l; y])
                  ([f; l; u; t; t; e; r] ++ [b; y]).
  Proof.
    intros.
    change [b; u; t; t; e; r] with ([b] ++ [u; t; t; e; r]).
    change [f; l; u; t; t; e; r] with ([f; l] ++ [u; t; t; e; r]).
    remember [u; t; t; e; r] as utter. clear Hequtter.

    Check app_assoc. rewrite <- app_assoc. rewrite <- app_assoc.
    Check perm_trans. apply perm_trans with (l' := utter ++ [f; l; y] ++ [b]).
    - rewrite (app_assoc utter [f; l; y]).
      Check Permutation_app_comm. apply Permutation_app_comm.
    - eapply perm_trans.
      2: apply Permutation_app_comm.
      rewrite <- app_assoc.
      Search (Permutation (_ ++ _) (_ ++ _)).
      apply Permutation_app_head.
      eapply perm_trans.
      2: apply Permutation_app_comm.
      simpl.
      Check perm_skip.
      do 2 apply perm_skip.
      Search (Permutation (_ :: _) (_ :: _)).
      apply perm_swap.
  Qed.



  Check perm_skip.
  Check Permutation_refl.
  Check Permutation_app_comm.
  Check app_assoc.

  Example permut_example: forall (a b: list nat),
      Permutation (5 :: 6 :: a ++ b) ((5 :: b) ++ (6 :: a ++ [])).
  Proof.
    intros.
    Search ((_ :: _) ++ _).
    rewrite <- (app_comm_cons b (6 :: a ++ []) 5).
    apply perm_skip.
    Check Permutation_app_comm. Search (_ ++ []). rewrite <- app_nil_end.
    apply (Permutation_app_comm (6 :: a) b).
  Qed.


  Check Permutation_cons_inv.
  Check Permutation_length_1_inv.

  Example not_a_permutation:
    ~ Permutation [1; 1] [1; 2].
  Proof.
    unfold not. intros H.
    apply Permutation_cons_inv in H.
    apply Permutation_length_1_inv in H. inversion H.
  Qed.


  Theorem maybe_swap_perm: forall l,
      Permutation l (maybe_swap l).
  Proof.
    intros.
    destruct l as [| h t] eqn:El.
    - simpl. reflexivity.
    - destruct t as [| h' t'] eqn:Et.
      + simpl. Check Permutation_refl. apply Permutation_refl.
      + simpl. bdestruct (h' <? h).
        * Search (Permutation (_ :: _) (_ :: _)). apply perm_swap.
        * reflexivity.
  Qed.




  Definition first_le_second (l: list nat): Prop :=
    match l with
    | f :: s :: _ => f <= s
    | _ => True
    end.

  Theorem maybe_swap_correct: forall l,
      Permutation l (maybe_swap l) /\ first_le_second (maybe_swap l).
  Proof.
    intro. split.
    - apply maybe_swap_perm.
    - destruct l as [| h t] eqn:El.
      + simpl. apply I.
      + destruct t as [| h' t'] eqn:Et.
        * simpl. apply I.
        * simpl. bdestruct (h' <? h).
          { simpl. omega. }
          { simpl. omega. }
  Qed.

End Exploration1.

Check Forall.

Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
    Permutation al bl ->
    Forall f al -> Forall f bl.
Proof.
  intros. generalize dependent bl.
  induction al; intros.
  - Search (Permutation [] _). apply Permutation_nil in H.
    rewrite H. assumption.
  - apply IHal.
Abort.


Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
    Permutation al bl ->
    Forall f al -> Forall f bl.
Proof.
  intros. generalize dependent bl. induction H0.
  - intros. apply Permutation_nil in H. rewrite H.
    Search (Forall _ []). apply Forall_nil.
  - intros. apply IHForall.
Abort.


Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
    Permutation al bl ->
    Forall f al -> Forall f bl.
Proof.
  intros. generalize dependent al. induction bl; intros.
  - apply Forall_nil.
  - Search (Forall _ (_ :: _)). apply Forall_cons.
    + destruct al as [| h t] eqn:Eal.
      * apply Permutation_nil in H. inversion H.
      * inversion H0. subst.
Abort.
