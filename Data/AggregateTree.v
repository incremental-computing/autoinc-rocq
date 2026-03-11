From Stdlib Require Import List Lia Compare_dec PeanoNat Eqdep_dec.
From AUTOINC Require Import EqDec Tactic.
Import ListNotations.

Hint Extern 4 => apply nat_EqDec : core.

Global Ltac natb := repeat match goal with
| [H : (_ =? _)  = true |- _] => apply Nat.eqb_eq in H; subst
| [H : (_ =? _)  = false |- _] => apply Nat.eqb_neq in H
| [H : (_ <? _)  = true |- _] => apply Nat.ltb_lt in H
| [H : (_ <? _)  = false |- _] => apply Nat.ltb_ge in H
end; try lia.

Hint Extern 4 => lia : core.
(* Hint Extern 4 => natb : core. *)
Set Firstorder Depth 2.

Module Type STRICT_PRE_ORDER.
  Parameter E : Type.
  Parameter eqa_dec : forall (x y : E), {x = y} + {x <> y}.
  Parameter lta : E -> E -> Prop.
  Parameter lta_dec : forall (x y : E), sum (lta x y) (sum (x = y) (lta y x)).
  Parameter bottom : E.
  
  Notation "x '<=E' y" := (x = y \/ lta x y) (at level 50).
  Notation "x '>E' y" := (lta y x) (at level 50).
  Notation "x '<E' y" := (lta x y) (at level 50).
  
  
  Parameter lta_irrefl : forall (x : E), ~ x <E x.
  Parameter lta_trans : forall (x y z : E), x <E y -> y <E z -> x <E z.
  Parameter bottom_least : forall (x : E), bottom <=E x.
End STRICT_PRE_ORDER.
Module STRICT_PRE_ORDER_FACTS(Import P : STRICT_PRE_ORDER).  
  Lemma lta_antisym : forall (x y : E), x <E y -> ~ y <E x.
  Proof. intros. intro c. apply (lta_trans x y x) in c. apply lta_irrefl in c. all:assumption. Qed.
  Lemma lta_antisym2 : forall (x y : E), ~ x <E y -> ~ y <E x -> x = y.
  Proof. intros. destruct (lta_dec x y); firstorder. Qed.
  Lemma lta_eq_trans : forall (x y z : E), x <=E y -> y <=E z -> x <=E z.
  Proof. intros. destruct H; destruct H0; subst; auto. right. eapply lta_trans; eauto. Qed.

  Definition lta_bool (x y : E) : bool :=
    if lta_dec x y then true else false.
  Notation "x '<?E' y" := (lta_bool x y) (at level 50).
  Definition eqa_bool (x y : E) : bool :=
    if eqa_dec x y then true else false.
  Notation "x '=?E' y" := (eqa_bool x y) (at level 50).
  Lemma lta_bool_true : forall x y, x <?E y = true -> x <E y.
  Proof. intros. unfold lta_bool in H. dest_match; auto. Qed.
  Lemma lta_bool_false : forall x y, x <?E y = false -> y <=E x.
  Proof. intros. unfold lta_bool in H. dest_match; auto. 
    destruct s; subst; auto.
  Qed.
  Lemma lta_true_bool : forall x y, x <E y -> x <?E y = true.
  Proof. intros. unfold lta_bool. dest_match; auto. destruct s.
    - subst. apply lta_irrefl in H. auto.
    - apply lta_antisym in H. auto.
  Qed.
  Lemma lta_false_bool : forall x y, ~ x <E y -> x <?E y = false.
  Proof. intros. unfold lta_bool. dest_match; auto. contradiction. Qed.

  Lemma eqa_bool_true : forall x y, x =?E y = true -> x = y.
  Proof. intros. unfold eqa_bool in H. dest_match; auto. Qed.
  Lemma eqa_bool_false : forall x y, x =?E y = false -> ~ (x = y).
  Proof. intros. unfold eqa_bool in H. dest_match; auto. Qed.

  Hint Resolve lta_irrefl : core.
  Hint Resolve lta_antisym : core.
  Hint Resolve lta_antisym2 : core.
  Hint Resolve lta_trans : core.

  Ltac lta_solve := 
  subst; repeat match goal with
  | [ H : ?elem <> ?elem |- _ ] => contradiction H
  | [ H : ?elem <E ?elem |- _ ] => contradict H; apply lta_irrefl
  | [ |- ~ (?x <E ?x) ] => apply lta_irrefl
  | [ H : _ = _ \/ _ <E _ |- _ ] => destruct H
  | [ H : ?x <E ?y, H1 : ?y <E ?x |- _ ] => apply lta_antisym in H; contradiction
  | [|- bottom <=E _] => apply bottom_least
  | [ H : ?x <E ?y |- ~ ?y <E ?x ] => apply lta_antisym; assumption
  | [ H : _ <?E _ = true |- _ ] => apply lta_bool_true in H
  | [ H : _ <?E _ = false |- _ ] => apply lta_bool_false in H
  | [ |- _ <?E _ = true ] => apply lta_true_bool
  | [ |- _ <?E _ = false ] => apply lta_false_bool
  | [ H : _ =?E _ = true |- _ ] => apply eqa_bool_true in H; subst
  | [ H : _ =?E _ = false |- _ ] => apply eqa_bool_false in H
  end.
  Hint Extern 4 => lta_solve : core.
End STRICT_PRE_ORDER_FACTS.

(* Module MinPairOrder(P1 : STRICT_PRE_ORDER)(P2 : STRICT_PRE_ORDER) <: STRICT_PRE_ORDER.
  Definition E := (P1.E * P2.E)%type.
  Lemma eqa_dec : forall (x y : E), {x = y} + {x <> y}.
  Proof.
    intros [x1 x2] [y1 y2].
    pose proof (P1.eqa_dec x1 y1) as [H1 | H2]; subst;
    pose proof (P2.eqa_dec x2 y2) as [H3 | H4]; subst;
    firstorder;
    right; unfold "<>"; intros; x_inj; auto.
  Qed.

  Definition lta (x y : E) : Prop :=
    match x, y with
    | (x1, x2), (y1, y2) => P1.lta x1 y1 /\ P2.lta x2 y2
    end.
  Lemma lta_dec : forall (x y : E), sum (lta x y) (sum (x = y) (lta y x)).
  Proof.
    intros [x1 x2] [y1 y2]; unfold lta.
    pose proof (P1.lta_dec x1 y1) as [H1 | [H2 | H3]];
    pose proof (P2.lta_dec x2 y2) as [H4 | [H5 | H6]]; subst; firstorder.
    - left; auto. 
  Abort.
Fail End MinPairOrder. *)

Module NatPreOrder <: STRICT_PRE_ORDER.
  Definition E := nat.
  Definition eqa_dec : forall (x y : E), {x = y} + {x <> y}.
  Proof.
    intros. destruct (eq_dec x y); auto.
  Qed.
  Definition lta : E -> E -> Prop := Nat.lt.
  Lemma lta_dec : forall (x y : E), sum (lta x y) (sum (x = y) (lta y x)).
  Proof.
    intros x y. unfold lta.
    destruct (lt_dec x y); auto.
    right.
    destruct (eq_dec x y); auto.
  Qed.
  Definition bottom : E := 0.
  
  Notation "x '<=E' y" := (x = y \/ lta x y) (at level 50).
  Notation "x '>E' y" := (lta y x) (at level 50).
  Notation "x '<E' y" := (lta x y) (at level 50).
  
  
  Lemma lta_irrefl : forall (x : E), ~ x <E x.
  Proof. intros. unfold lta. lia. Qed. 
  Lemma lta_trans : forall (x y z : E), x <E y -> y <E z -> x <E z.
  Proof. unfold lta; lia. Qed.
  Lemma bottom_least : forall (x : E), bottom <=E x.
  Proof. unfold lta, bottom; auto. Qed.
End NatPreOrder.


(* Module MaxPairNatPreOrder <: STRICT_PRE_ORDER.
  Definition E := (nat * nat)%type.
  Lemma eqa_dec : forall (x y : E), {x = y} + {x <> y}.
  Proof.
    intros [x1 x2] [y1 y2].
    destruct (eq_dec x1 y1), (eq_dec x2 y2); subst; auto;
    right; unfold "<>"; intros; x_inj; auto.
  Qed.
  Definition lta x y := fst x + snd x < fst y + snd y.
  Lemma lta_dec : forall (x y : E), sum (lta x y) (sum (x = y) (lta y x)).
  Abort.
Fail End MaxPairNatPreOrder. *)



Module Type JOIN (Import PreOrd : STRICT_PRE_ORDER).
  Module Import PreOrdFacts := STRICT_PRE_ORDER_FACTS(PreOrd).

  Parameter join : E -> E -> E.
  Parameter join_assoc : forall (x y z : E), join x (join y z) = join (join x y) z.
  Parameter join_comm : forall (x y : E), join x y = join y x.
  (* Parameter join_idempotent : forall (x : E), join x x = x. *)

  Parameter join_upper_l : forall (x y : E), x <=E join x y.
  Parameter join_upper_r : forall (x y : E), y <=E join x y.
  Parameter join_least : forall (x y z : E), x <=E z -> y <=E z -> join x y <=E z.
  Parameter join_eq_l : forall (x y : E), join x y <=E x -> join x y = x.
  Parameter join_eq_r : forall (x y : E), join x y <=E y -> join x y = y.

  Lemma join_bottom_l : forall (x : E), join bottom x = x.
  Proof. intros. rewrite join_eq_r; auto. apply join_least; auto. Qed.
  Lemma join_bottom_r : forall (x : E), join x bottom = x.
  Proof. intros. rewrite join_eq_l; auto. apply join_least; auto. Qed.
  
  Lemma join_le : forall (x x' y y' : E), 
    x <=E x' -> y <=E y' -> join x y <=E join x' y'.
  Proof. 
    intros. apply join_least. 
    - eapply lta_eq_trans; eauto. apply join_upper_l.
    - eapply lta_eq_trans; eauto. apply join_upper_r.
  Qed.

  Ltac join_comm a b :=
    replace (join a b) with (join b a); try apply join_comm.

  (* Lemma join_idemp1 : forall a b,
    join a (join b a) = join a b.
  Proof.
    intros. rewrite join_assoc. join_comm a b. rewrite <- join_assoc. rewrite join_idempotent. reflexivity.
  Qed. *)

  (* Lemma join_idemp2 : forall a b c,
    join a (join b (join c a)) = join a (join b c).
  Proof.
    intros. rewrite join_assoc. join_comm a b. rewrite <- join_assoc.
    rewrite join_idemp1. rewrite join_assoc. join_comm b a. rewrite join_assoc. reflexivity.
  Qed. *)

  Ltac join_reduce := 
    repeat ((
      (* rewrite join_idempotent || rewrite join_idemp1 || rewrite join_idemp2 ||  *)
      rewrite join_bottom_l || rewrite join_bottom_r || apply join_le); eauto).
  
  Ltac join_solve := 
    join_reduce; repeat rewrite join_assoc; join_reduce; repeat rewrite <- join_assoc; join_reduce; try reflexivity.
  
  Hint Extern 4 => join_solve : core.
  Hint Resolve join_comm : core.
End JOIN.

Module AggregateTree (Import PreOrd : STRICT_PRE_ORDER) (Join : JOIN(PreOrd)).
  Import PreOrd.
  Module Import F := STRICT_PRE_ORDER_FACTS(PreOrd).
  Import Join.
  
  (* Aggregate tree (AT) is a binary tree with aggregate result *)
  Inductive AT : Type := 
  | Empty : AT
  | Node (res : E) (elem : E) (count : nat) (l r : AT) : AT
  .

  Definition result (t : AT) : E :=
    match t with
    | Empty => bottom
    | Node res _ _ _ _ => res
    end.

  Fixpoint elem_join (elem : E) (count : nat) : E := 
  match count with
  | 0 => bottom
  | 1 => elem
  | S count => join (elem_join elem count) elem
  end.

  (* Definition result_comp (elem : E) (count : nat) (lres rres : E) : E := 
    join (join lres rres) (elem_join elem count).
  Hint Unfold result_comp : core. *)

  Notation result_comp elem count lres rres := (join (join lres rres) (elem_join elem count)).

  Definition node (elem : E) (count : nat) (l r : AT) : AT := 
    Node (result_comp elem count (result l) (result r)) elem count l r.
  
  Fixpoint AT_In (x : E) (t : AT) : Prop :=
    match t with 
    | Empty => False
    | Node _ elem c l r => x = elem \/ AT_In x l \/ AT_In x r
    end.

  Fixpoint AT_All (P : E -> Prop) (t : AT) : Prop :=
    match t with 
    | Empty => True
    | Node _ elem _ l r => P elem /\ AT_All P l /\ AT_All P r
    end.

  Definition AT_lt x t := AT_All (fun a => x <E a) t.
  Definition AT_le x t := AT_All (fun a => x <=E a) t.
  Definition AT_gt x t := AT_All (fun a => x >E a) t.

  Lemma AT_lt_le : forall x t,
    AT_lt x t -> AT_le x t.
  Proof.
    induction t; firstorder idtac.
  Qed.

  Lemma AT_lt_trans : forall x y t,
    x <E y -> AT_lt y t -> AT_lt x t.
  Proof.
    induction t; firstorder; eauto.
  Qed.

  Lemma AT_le_trans : forall x y t,
    x <E y -> AT_le y t -> AT_lt x t.
  Proof.
    induction t; firstorder. eauto.
  Qed.

  Lemma AT_gt_trans : forall x y t,
    x >E y -> AT_gt y t -> AT_gt x t.
  Proof.
    induction t; firstorder. eauto.
  Qed.

  Lemma AT_le_gt : forall res elem c l r a b,
    AT_le a (Node res elem c l r) -> AT_gt b (Node res elem c l r) -> a <E b.
  Proof.
    intros. assert (a <=E elem). inversion H; auto.
    assert (b >E elem). inversion H0; auto. 
    x_inv H1; eauto.
  Qed.

  Fixpoint BST (t : AT) : Prop :=
    match t with 
    | Empty => True
    | Node res elem count l r => AT_gt elem l /\ count > 0 /\ AT_lt elem r /\ BST l /\ BST r
    end.

  Fixpoint insert (t : AT) (x : E) : AT :=
    match t with
    | Empty => Node x x 1 Empty Empty
    | Node res elem c l r => 
      if eqa_dec x elem
      then node elem (S c) l r
      else if lta_dec x elem
          then node elem c (insert l x) r
          else node elem c l (insert r x)
    end.

  Lemma AT_In_insert_id : forall t a,
    AT_In a (insert t a).
  Proof.
    induction t; intros; simpl; auto 1;
    dest_match; simpl; auto. 
  Qed.

  Hint Resolve AT_In_insert_id : core.
  
  Lemma AT_In_insert : forall t a x,
    AT_In a (insert t x) <-> a = x \/ AT_In a t.
  Proof.
    induction t; split; intros; simpl; 
    simpl in H; auto 1; dest_match; 
    inversion H; subst; auto 2;
    try rewrite ?IHt1 in *;
    try rewrite ?IHt2 in *;
    simpl; auto 4; x_dest; subst; firstorder (auto 0).
  Qed.

  Lemma AT_All_insert : forall P x t,
    P x -> AT_All P t -> AT_All P (insert t x).
  Proof.
    intros. induction t; firstorder.
    simpl. dest_match; repeat constructor; auto.
  Qed.
  
  Hint Resolve AT_All_insert : core.

  Lemma BST_insert : forall x t,
    BST t -> BST (insert t x).
  Proof.
    intros. induction t. repeat constructor.
    destruct H as [H0 [H1 [H2 [H3 H4]]]].
    simpl.
    dest_match; constructor; auto 2.
    - firstorder.
    - unfold AT_gt; auto.
    - firstorder.
    - repeat split; auto 3. simpl in *. x_dest; auto. 
      unfold AT_lt in *. eapply AT_All_insert; auto.
      destruct s; subst; auto.
  Qed.  

  Fixpoint delete_min (t : AT) : option (E * nat * AT) :=
    match t with
    | Empty => None
    | Node _ elem c Empty r => Some (elem, c, r)
    | Node res elem c l r => 
      match delete_min l with
      | None => None
      | Some (elem', c', l') => Some (elem', c', node elem c l' r)
      end
    end.

  Definition delete_root (t : AT) : AT :=
    match t with
    | Empty => Empty
    | Node _ _ _ l Empty => l
    | Node _ _ _ l r => 
      match delete_min r with
      | None => r
      | Some (m,c,r') => node m c l r'
      end
    end.

  Fixpoint delete (t : AT) (x : E) : AT :=
    match t with
    | Empty => t
    | Node res elem c l r =>
      if eqa_dec x elem
      then if lt_dec 1 c
           then node elem (pred c) l r
           else delete_root t
      else if lta_dec x elem
           then node elem c (delete l x) r
           else node elem c l (delete r x)
    end.

  Lemma AT_In_min : forall (t : AT) (a : E) c t',
    delete_min t = Some (a,c,t') -> AT_In a t.
  Proof.
    induction t; intros.
    - inversion H.
    - simpl in H. dest_match; try discriminate; x_inj. 
      firstorder.
      right. left. eapply IHt1. eauto.
  Qed.

  Lemma AT_All_In : forall P t x,
    AT_All P t -> AT_In x t -> P x.
  Proof.
    induction t; intros x Hall Hin.
    - inversion Hin.
    - simpl in *. x_dest; subst; auto.
  Qed.

  Lemma AT_All_min : forall P (t : AT) (a : E) c t',
    AT_All P t -> delete_min t = Some (a,c,t') -> P a.
  Proof.
    intros. eapply AT_All_In; try eapply AT_In_min; eauto.
  Qed.

  Lemma AT_All_minrest : forall P (t : AT) (a : E) c t',
    AT_All P t -> delete_min t = Some (a,c,t') -> AT_All P t'.
  Proof.
    induction t; intros.
    - inversion H0.
    - destruct H as [H1 [H2 H3]]. inversion H0.
      dest_match; try x_inj.
      + firstorder.
      + simpl in *; x_dest; repeat split; auto 1.  
        eapply IHt1; eauto.
      + congruence.      
  Qed.

  Lemma AT_All_delete : forall P t x,
    AT_All P t -> AT_All P (delete t x).
  Proof. 
    induction t; intros; auto.
    destruct H as [H1 [H2 H3]].
    simpl. 
    dest_match; simpl in *; auto 4; repeat split; auto 1; x_dest.
    - eapply (AT_All_min P (Node res0 elem0 count0 a1 a2)); eauto; firstorder.
    - eapply (AT_All_minrest P (Node res0 elem0 count0 a1 a2)); eauto; firstorder.
  Qed.

  Lemma BST_minrest : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> BST t'.
  Proof.
    induction t; intros. discriminate.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl in H0.
    dest_match; simpl in *; auto 4; repeat split; x_dest; try x_inj; auto 1; simpl.
    - repeat split; auto 1. unfold AT_gt.  
      eapply (AT_All_minrest _ (Node res0 elem0 count0 a0_1 a0_2)); firstorder; eauto.
      eapply IHt1; firstorder.
    - congruence.
  Qed.

  Hint Extern 4 => congruence : core.

  Lemma Poscount_min : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> c > 0.
  Proof.
    induction t; intros. discriminate.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl in H0. 
    dest_match; simpl in *; auto 4; repeat split; x_dest; try x_inj; auto 1; simpl.    
    eapply IHt1; firstorder.
  Qed.
  
  Lemma delete_min_is_min : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> AT_le a t.
  Proof.
    induction t; intros. constructor.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl in H0. dest_match; try x_inj; auto 1.
    - unfold AT_le; simpl in *. repeat split; auto.  
      apply AT_lt_le; auto.
    - assert (AT_le a (Node res0 elem0 count0 a0_1 a0_2)). eapply IHt1; eauto.
      clear IHt1 IHt2.
      unfold AT_le in *. simpl in *; x_dest; repeat split; subst; firstorder (eauto 2).
      + apply AT_lt_le. eapply AT_lt_trans; eauto.
      + apply AT_lt_le; eauto. apply AT_lt_trans with (y := elem); eauto.
  Qed.

  Lemma delete_min_is_minrest : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> AT_lt a t'.
  Proof.
    induction t; intros. inversion H0.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl in H0. destruct t1.
    - x_inj. auto.
    - destruct (delete_min (Node res0 elem0 count0 t1_1 t1_2)) as [[[min mincount] rest]|] eqn:E; try discriminate.
      x_inj. assert (a <E elem).
      * eapply AT_le_gt; eauto. eapply delete_min_is_min; eauto.
      * unfold AT_lt in *; simpl in *; x_dest; subst; repeat split; auto 1.
        eapply IHt1; eauto. 
        apply AT_lt_trans with (y := elem); auto.
  Qed.

  Lemma BST_delete : forall t x,
    BST t -> BST (delete t x).
  Proof.
    induction t; intros; auto.
    destruct H as [H0 [H1 [H2 [H3 H4]]]].
    simpl. dest_match; try x_inj; auto 1. 
    - firstorder.
    - apply delete_min_is_minrest in EQ1 as EQ2; auto.
      apply delete_min_is_min in EQ1 as EQ3; auto.
      apply BST_minrest in EQ1 as EQ4; auto.
      apply Poscount_min in EQ1 as EQ5; auto.
      apply AT_In_min in EQ1 as EQ6. 
      apply (AT_All_In (fun a => elem <E a)) in EQ6; auto 1.
      firstorder (auto 1). all:eauto using AT_gt_trans.
    - simpl; repeat split; auto 2. apply AT_All_delete. auto.
    - simpl; repeat split; auto 2. apply AT_All_delete. auto.
  Qed.

  Fixpoint AggT (t : AT) : Prop :=
    match t with 
    | Empty => True
    | Node res elem count l r => 
      res = result_comp elem count (result l) (result r) /\ AggT l /\ AggT r
    end.

  Lemma Aggregate_insert : forall t x,
    AggT t -> result (insert t x) = join (result t) x.
  Proof.
    induction t; intros; auto.
    destruct H as [A0 [A1 A2]]. subst.
    simpl. dest_match; simpl; auto 2.
    - dest_match. simpl. auto 2. join_solve.
    - rewrite IHt1; auto. 
      join_solve. f_equal. rewrite join_comm. auto.
    - rewrite IHt2; auto.
      join_solve. f_equal. f_equal. auto.
  Qed.

  Lemma AggT_insert : forall t x,
    AggT t -> AggT (insert t x).
  Proof.
    induction t; intros. simpl. auto 2.
    simpl. dest_match; firstorder. 
  Qed.

  Lemma AggT_minrest : forall (t : AT) (a : E) c t',
    AggT t -> delete_min t = Some (a,c,t') -> AggT t'.
  Proof.
    induction t; intros. discriminate.
    destruct H as [H1 [H2 H3]]. inversion H0. 
    dest_match; try x_inj; firstorder.
    eapply IHt1; firstorder.
  Qed.

  Lemma AggT_delete : forall t x,
    AggT t -> AggT (delete t x).
  Proof.
    induction t; intros. auto.
    destruct H as [A0 [A1 A2]]. subst.
    simpl. dest_match; firstorder.
    eapply AggT_minrest. 2:eauto. firstorder.
  Qed.

  Fixpoint count (x : E) (t : AT) : nat :=
    match t with
    | Empty => 0
    | Node res elem c l r =>
      if eqa_dec x elem
      then c
      else if lta_dec x elem
           then count x l
           else count x r
    end.
  
  Lemma count_lt : forall x t,
    AT_lt x t -> count x t = 0.
  Proof. 
    induction t; firstorder. 
    simpl. dest_match; auto.
  Qed.

  Lemma count_gt : forall x t,
    AT_gt x t -> count x t = 0.
  Proof. 
    induction t; firstorder. 
    simpl. dest_match; auto.
  Qed.

  Hint Extern 4 => apply count_lt : core.
  Hint Extern 4 => apply count_gt : core.

  Lemma count_insert : forall x t,
    count x (insert t x) = S (count x t).
  Proof.  
    induction t; simpl.
    - dest_match; auto.
    - dest_match; simpl; dest_match; auto.
  Qed.

  Lemma count_insert_rest : forall t x a,
    BST t -> x <> a -> count x (insert t a) = count x t.
  Proof.  
    induction t; intros; simpl.
    - dest_match; auto.
    - destruct H as [H1 [H2 [H3 [H4 H5]]]].
      dest_match; simpl; dest_match; auto.
  Qed.

  Lemma count_delete_min : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> count a t = c.
  Proof.
    induction t; intros. discriminate.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl. dest_match.
    - simpl in H0. dest_match; try discriminate; x_inj; auto.
      apply delete_min_is_min in EQ0; auto.
      eapply AT_le_gt in EQ0; eauto; auto.
    - simpl in H0. dest_match; try discriminate; x_inj; auto.
      eapply IHt1; eauto.
    - apply delete_min_is_minrest in H0 as H6; firstorder.
      simpl in H0. dest_match; try discriminate; x_inj; firstorder.
      destruct s; subst; auto.
  Qed.
  
  Lemma count_delete_minrest : forall t a c t',
    BST t -> delete_min t = Some (a,c,t') -> count a t' = 0.
  Proof.
    induction t; intros. discriminate. clear IHt2.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    apply delete_min_is_min in H0 as Hmin. 2: firstorder.
    apply delete_min_is_minrest in H0 as Hminrest. 2: firstorder.
    simpl in H0. dest_match; try discriminate; x_inj; auto.
  Qed.

  Lemma count_delete_min_rest : forall t a c t' x,
    BST t -> delete_min t = Some (a,c,t') -> a <> x -> count x t' = count x t.
  Proof.
    induction t; intros. discriminate. clear IHt2.
    destruct H as [H6 [H2 [H3 [H4 H5]]]].
    simpl in H0. dest_match; try discriminate; x_inj; auto.
    - simpl. dest_match; natb; auto. apply count_lt. eapply AT_lt_trans with (y := a); eauto.
    - simpl. destruct (eqa_dec x elem) eqn:EE1; auto. 
      destruct (lta_dec x elem) eqn:EE2; auto.
      eapply IHt1; eauto.
  Qed.

  Lemma count_delete_root : forall res x c l r,
    BST (Node res x c l r) -> count x (delete_root (Node res x c l r)) = 0.
  Proof. 
    intros.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl. dest_match; auto. 
    eapply AT_All_min in EQ as EQmin. 2: apply H3. simpl in EQmin.
    unfold node. simpl. dest_match; auto.
    destruct s; subst; auto.
  Qed.

  Lemma delete_min_Some : forall l res x c r,
    exists p, delete_min (Node res x c l r) = Some p.
  Proof.
    induction l; intros; simpl; eauto.
    dest_match; try discriminate; eauto; try x_inj.
    remember (Node res1 elem0 count1 a1 a2) as l.
    destruct (IHl1 res x c r). simpl in H. rewrite EQ0 in H.
    rewrite Heql in H. discriminate.
  Qed.

  Lemma delete_min_None : forall l res x c r,
    delete_min (Node res x c l r) <> None.
  Proof.
    intros. destruct (delete_min_Some l res x c r). rewrite H. intro a. discriminate. 
  Qed.
  
  Lemma count_delete_root_rest_l : forall res x c l r a,
    BST (Node res a c l r) -> x <E a -> count x (delete_root (Node res a c l r)) = count x l.
  Proof. 
    intros.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl. dest_match; auto. 
    - eapply AT_All_min in EQ as EQmin. 2: apply H3. simpl in EQmin.
      simpl. dest_match; auto. lta_solve; auto. assert (a <E x); eauto.
      destruct s; subst; auto.
      eapply lta_trans; eauto.
    - apply delete_min_None in EQ. auto.
  Qed.

  Lemma count_delete_root_rest_r : forall res x c l r a,
    BST (Node res a c l r) -> x >E a -> count x (delete_root (Node res a c l r)) = count x r.
  Proof. 
    intros.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    simpl. dest_match; auto.
    rewrite count_gt; auto. eapply AT_gt_trans; eauto.
    remember (Node res0 elem count0 a0_1 a0_2) as r.
    destruct (eqa_dec x e) eqn:E; lta_solve.
    - apply count_delete_min in EQ; auto. rewrite EQ. simpl. dest_match; auto.
    - apply delete_min_is_min in EQ as ?; auto.
      apply delete_min_is_minrest in EQ as ?; auto.
      destruct (lta_dec x e) eqn:E2; auto; lta_solve; auto.
      * simpl. dest_match; lta_solve; auto. firstorder.
        + rewrite count_gt; auto. 2: eapply AT_gt_trans; eauto.
          rewrite count_lt; auto. eapply AT_le_trans in H; eauto. firstorder.
        + rewrite count_gt; auto. 2: eapply AT_gt_trans in H0; eauto.
          rewrite count_lt; auto. eapply AT_le_trans in H; eauto. firstorder.
      * apply count_delete_min_rest with (x:=x) in EQ as Hmin; auto. rewrite <- Hmin. clear Hmin.
        simpl. dest_match; auto.
  Qed.

  Lemma count_delete : forall x t,
    BST t -> count x (delete t x) = pred (count x t).
  Proof.  
    induction t; intros; auto.
    destruct H as [? [? [? [? ?]]]].
    unfold delete. dest_match; natb; auto 1.
    - simpl. dest_match; auto.
    - rewrite count_delete_root; auto. 
      simpl; dest_match; auto. firstorder.
    - simpl. dest_match; natb; auto.
    - simpl. dest_match; natb; auto.
  Qed.

  Lemma count_delete_rest : forall t x a,
    BST t -> x <> a -> count x (delete t a) = count x t.
  Proof.
    induction t; intros; auto.
    destruct H as [? [? [? [? ?]]]].
    unfold delete. 
    dest_match; natb; auto 1; try (simpl; dest_match; natb; auto 2; fail).
    destruct (lta_dec x elem) eqn:E; lta_solve; auto.
    - rewrite count_delete_root_rest_l; auto 1. 2: firstorder.
      simpl. dest_match; auto.
    - rewrite count_delete_root_rest_r; auto 1. 2: firstorder.
      simpl. dest_match; auto.
      destruct s; subst; auto.
  Qed.

End AggregateTree.
