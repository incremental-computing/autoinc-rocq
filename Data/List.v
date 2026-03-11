(* Miscellaneous operations on lists (that are not in the standard library) *)
From Stdlib Require Import List Lia.
From AUTOINC Require Import Tactic.
Import ListNotations.
Set Implicit Arguments.
Section ListMul.
  Variable A : Type.
  Fixpoint list_mul (m : nat) (n : A) := 
    match m with O => [] | S m => n :: (list_mul m n) end.

  Lemma list_mul_app : forall m1 m2 n,
    list_mul m1 n ++ list_mul m2 n = list_mul (m1 + m2) n.
  Proof.
    induction m1; simpl; intros; auto.
    rewrite IHm1; auto.
  Qed.

  Corollary list_mul_app_comm : forall m1 m2 n,
    list_mul m1 n ++ list_mul m2 n = list_mul m2 n ++ list_mul m1 n.
  Proof.
    intros.
    repeat rewrite list_mul_app.
    assert (m1 + m2 = m2 + m1). lia. rewrite H. 
    reflexivity.
  Qed.
  Lemma list_mul_id : forall n, [n] = list_mul 1 n.
  Proof. intros. simpl. auto. Qed.

  Lemma list_mul_cons : forall m n,
    n :: (list_mul m n) = list_mul (1 + m) n.
  Proof.
    intros. simpl. auto.
  Qed.

  Lemma list_mul_cons_tail : forall m n,
    (list_mul m n) ++ [n] = list_mul (1 + m) n.
  Proof.
    intros. simpl. rewrite list_mul_id, list_mul_cons, list_mul_app; f_equal; lia. 
  Qed.

  Lemma firstn_trim : forall (x : list A) i n , n < i ->
    firstn i x = firstn n x ++ firstn (i - n) (skipn n x).
  Proof.
    x_ind x; simpl.
    - rewrite !firstn_nil, skipn_nil, firstn_nil; auto; simpl.
    - destruct i, n; simpl; auto. lia.
      f_equal.
      eapply IHx. lia.
  Qed.

  Lemma firstn_not_in : forall (x : list A) i c,
    ~ In c x -> ~In c (firstn i x).
  Proof. 
    x_ind x; intros ?.
    rewrite firstn_nil in H0; auto.
    firstorder.
    destruct i; simpl in *. auto.
    destruct H0; auto.
    eapply IHx in H1.
    eauto.
  Qed.

  Lemma skipn_not_in : forall (x : list A) i c,
    ~ In c x -> ~In c (skipn i x).
  Proof. 
    x_ind x; intros ?.
    rewrite skipn_nil in H0; auto.
    firstorder.
    destruct i; simpl in *. auto.
    destruct H0; auto.
    eapply IHx in H1.
    eauto.
  Qed.

  Lemma firstn_in : forall (x : list A) i c,
    In c (firstn i x) -> In c x.
  Proof. 
    x_ind x; rewrite ?firstn_nil in *; auto.
    destruct i; simpl in *; firstorder.
  Qed.

  Lemma skipn_in : forall (x : list A) i c,
    In c (skipn i x) -> In c x.
  Proof. 
    x_ind x; 
    rewrite ?skipn_nil in *; auto.
    destruct i; simpl in *; firstorder.
  Qed.

  Hint Extern 4 => lia : core.

  Lemma skipn_in_more : forall (x : list A) i j c,
    i >= j -> In c (skipn i x) -> In c (skipn j x).
  Proof.
    x_ind x; rewrite ?skipn_nil in * ; simpl in *; auto.
    destruct i, j; simpl in *; firstorder.
    right.
    apply skipn_in in H0; auto.
  Qed.

  
End ListMul.




