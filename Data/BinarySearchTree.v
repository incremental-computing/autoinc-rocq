From Stdlib Require Import List Lia Compare_dec PeanoNat Eqdep_dec.
From AUTOINC Require Import EqDec Tactic.
Import ListNotations.

Hint Extern 4 => apply nat_EqDec : core.
Hint Extern 4 => lia : core.

Section BinarySearchTree.
  Definition A : Type := nat.
  
  (* Binary tree (BT) *)
  Inductive BT : Type := 
  | Empty : BT
  | Node (elem : A) (count : nat) (l r : BT) : BT
  .

  Fixpoint BT_In (x : A) (t : BT) : Prop :=
    match t with 
    | Empty => False
    | Node elem c l r => x = elem \/ BT_In x l \/ BT_In x r
    end.

  Fixpoint BT_All (P : A -> Prop) (t : BT) : Prop :=
    match t with 
    | Empty => True
    | Node elem _ l r => P elem /\ BT_All P l /\ BT_All P r
    end.

  Definition BT_lt x t := BT_All (fun a => x < a) t.
  Definition BT_le x t := BT_All (fun a => x <= a) t.
  Definition BT_gt x t := BT_All (fun a => x > a) t.

  Lemma BT_lt_le : forall x t,
    BT_lt x t -> BT_le x t.
  Proof.
    induction t; firstorder.
  Qed.

  Lemma BT_lt_trans : forall x y t,
    x < y -> BT_lt y t -> BT_lt x t.
  Proof.
    induction t; firstorder.
  Qed.

  Lemma BT_gt_trans : forall x y t,
    x > y -> BT_gt y t -> BT_gt x t.
  Proof.
    induction t; firstorder.
  Qed.

  Lemma BT_le_gt : forall elem c l r a b,
    BT_le a (Node elem c l r) -> BT_gt b (Node elem c l r) -> a < b.
  Proof.
    intros. assert (a <= elem). inversion H; auto.
    assert (b > elem). inversion H0; auto. 
    lia.
  Qed.

  Fixpoint BST (t : BT) : Prop :=
    match t with 
    | Empty => True
    | Node elem count l r => BT_gt elem l /\ count > 0 /\ BT_lt elem r /\ BST l /\ BST r
    end.

  Fixpoint insert (x : A) (t : BT) : BT :=
    match t with
    | Empty => Node x 1 Empty Empty
    | Node elem c l r => 
      if x =? elem
      then Node elem (S c) l r
      else if x <? elem
          then Node elem c (insert x l) r
          else Node elem c l (insert x r)
    end.
  
  Lemma BT_All_insert : forall P x t,
    P x -> BT_All P t -> BT_All P (insert x t).
  Proof.
    intros. induction t; firstorder.
    simpl. dest_match; repeat constructor; auto.
  Qed.

  Lemma BST_insert : forall x t,
    BST t -> BST (insert x t).
  Proof.
    intros. induction t. repeat constructor.
    inversion H as [H0 [H1 [H2 [H3 H4]]]].
    simpl. dest_match; constructor; auto; repeat split; auto.
    - apply BT_All_insert. apply Nat.ltb_lt. all:assumption.
    - apply BT_All_insert. apply Nat.ltb_ge in EQ0. apply Nat.eqb_neq in EQ. lia. assumption.
  Qed.

  Fixpoint delete_min (t : BT) : option (A * nat * BT) :=
  match t with
  | Empty => None
  | Node elem c Empty r => Some (elem, c, r)
  | Node elem c l r => 
    match delete_min l with
    | None => None
    | Some (elem', c', l') => Some (elem', c', Node elem c l' r)
    end
  end.

  Definition delete_root (t : BT) : BT :=
  match t with
  | Empty => Empty
  | Node _ _ l Empty => l
  | Node _ _ l r => 
    match delete_min r with
    | None => r
    | Some (m,c,r') => Node m c l r'
    end
  end.

  Fixpoint delete (x : A) (t : BT) : BT :=
    match t with
    | Empty => t
    | Node elem c l r =>
      if x =? elem
      then if 1 <? c
           then Node elem (pred c) l r
           else delete_root t
      else if x <? elem
           then Node elem c (delete x l) r
           else Node elem c l (delete x r)
    end.

  Lemma BT_In_min : forall (t : BT) (a : A) c t',
    delete_min t = Some (a,c,t') -> BT_In a t.
  Proof.
    induction t; intros.
    - inversion H.
    - simpl in H. dest_match; try x_inj; firstorder.
      right. left. eapply IHt1. eauto.
  Qed.

  Lemma BT_All_In : forall P t x,
    BT_All P t -> BT_In x t -> P x.
  Proof.
    induction t; intros x Hall Hin.
    - inversion Hin.
    - simpl in *. firstorder. subst. assumption.
  Qed.

  Lemma BT_All_min : forall P (t : BT) (a : A) c t',
    BT_All P t -> delete_min t = Some (a,c,t') -> P a.
  Proof.
    intros. eapply BT_All_In; try eapply BT_In_min; eauto.
  Qed.

  Lemma BT_All_minrest : forall P (t : BT) (a : A) c t',
    BT_All P t -> delete_min t = Some (a,c,t') -> BT_All P t'.
  Proof.
    induction t; intros.
    - inversion H0.
    - destruct H as [H1 [H2 H3]]. inversion H0. dest_match; try x_inj; firstorder.
      eapply IHt1; firstorder.
  Qed.

  Lemma BT_All_delete : forall P t x,
    BT_All P t -> BT_All P (delete x t).
  Proof. 
    induction t; intros; auto.
    destruct H as [H1 [H2 H3]].
    simpl. dest_match; firstorder.
    eapply (BT_All_min P (Node elem0 count0 b1 b2)); eauto; firstorder.
    eapply (BT_All_minrest P (Node elem0 count0 b1 b2)); eauto; firstorder.
  Qed.

  Lemma BST_minrest : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> BST t'.
  Proof.
    induction t; intros. discriminate.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl in H0. dest_match; try x_inj; firstorder.
    eapply (BT_All_minrest _ (Node elem0 count0 b1 b2)); firstorder; eauto.
    eapply IHt1; firstorder.
  Qed.

  Lemma Poscount_minrest : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> c > 0.
  Proof.
    induction t; intros. discriminate.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl in H0. dest_match; try x_inj; firstorder.
    eapply IHt1; firstorder.
  Qed.
  
  Lemma delete_min_is_min : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> BT_le a t.
  Proof.
    induction t; intros. constructor.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl in H0. dest_match; try x_inj; auto.
    - firstorder using BT_lt_le.
    - assert (BT_le a (Node elem0 count0 b1 b2)). eapply IHt1; eauto.
      firstorder. apply BT_lt_le. apply BT_lt_trans with (y := elem); auto.
    - discriminate.
  Qed.

  Lemma delete_min_is_minrest : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> BT_lt a t'.
  Proof.
    induction t; intros. inversion H0.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl in H0. destruct t1.
    - x_inj. auto.
    - destruct (delete_min (Node elem0 count0 t1_1 t1_2)) as [[[min mincount] rest]|] eqn:E; try discriminate.
      x_inj. assert (a < elem). 
      * eapply BT_le_gt; eauto. eapply delete_min_is_min; eauto.
      * firstorder. eapply IHt1; eauto. firstorder. apply BT_lt_trans with (y := elem); auto.
  Qed.

  Lemma BST_delete : forall t x,
    BST t -> BST (delete x t).
  Proof.
    induction t; intros; auto.
    destruct H as [H0 [H1 [H2 [H3 H4]]]].
    simpl. dest_match; try x_inj; auto. 
    - apply Nat.ltb_lt in EQ0. firstorder.
    - apply delete_min_is_minrest in EQ1 as EQ2; auto.
      apply delete_min_is_min in EQ1 as EQ3; auto.
      apply BST_minrest in EQ1 as EQ4; auto.
      apply Poscount_minrest in EQ1 as EQ5; auto.
      apply BT_In_min in EQ1 as EQ6. apply (BT_All_In (fun a => elem < a)) in EQ6; auto.
      firstorder. eauto using BT_gt_trans.
    - firstorder. apply BT_All_delete. auto.
    - firstorder. apply BT_All_delete. assumption.
  Qed.

End BinarySearchTree.