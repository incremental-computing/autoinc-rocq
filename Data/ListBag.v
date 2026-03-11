From AUTOINC Require Import EqDec Tactic ListMap List Fold.
From Stdlib Require Import Compare_dec PeanoNat Lia List Classes.SetoidClass.

Import ListNotations.

Set Implicit Arguments.

Declare Scope bag_scope.
Open Scope bag_scope.



Hint Extern 4 => congruence : core.
Hint Extern 4 => lia : core.

Section Bag.

  Variable T : Type.

  Context `{EqT : EqDec T}.

  Definition bag := list T.
  
  Definition empty_bag : bag := [].

  Definition singleton a : bag := [a].

End Bag.
Arguments empty_bag {T}.

Section BagSupport.

  Variable T : Type.

  Context `{EqT : EqDec T}.

  Implicit Type a : T.
  Implicit Type b : bag T.
  Fixpoint support_helper b a n : nat :=
    match b with
    | [] => n
    | a' :: b => 
      let n' := if eq_dec a a' then S n else n in support_helper b a n'
    end.
  
  (* the support of an element a in the bag b. *)
  Definition support b a := support_helper b a O.

  Lemma support_default : forall b a n, support_helper b a n = n + support_helper b a O.
  Proof.
    induction b; intros; auto; simpl; dest_match; auto. 
    rewrite IHb; try lia. symmetry. rewrite IHb. lia.
  Qed.
  
  Lemma support_default_S : forall b a n, support_helper b a (S n) = (S n) + support_helper b a O.
  Proof.
    intros. rewrite support_default; auto.
  Qed. 

  Lemma support_not_in : forall b k n, ~ List.In k b -> support_helper b k n = n.
  Proof.
    induction b; intros; simpl in *; auto.
    dest_match; firstorder.
  Qed.

  Lemma support_cons : forall hd tl n, support (hd :: tl) n = 
    support tl n + (if eq_dec hd n then 1 else 0).
  Proof.
    unfold support; intros; simpl. dest_match; try rewrite !support_default_S; auto.
  Qed.

  Lemma support_nil : forall n, support [] n = 0.
  Proof. unfold support. easy. Qed.

  Definition support_dict_fold b init := 
    let f:= fun d : dict T nat => fun t : T =>  
      dict_add_with d t 1 (fun v => S v) in fold_left f b init.

  (* collect the non-zero support for each element in the bag. *)
  Definition support_dict b : dict T nat := support_dict_fold b dnil.

  Lemma support_dict_no_dup : forall b d, dict_no_dup d -> dict_no_dup (support_dict_fold b d).
  Proof.
    unfold dict_no_dup; induction b; intros; simpl; auto. apply IHb.
    apply dict_keys_no_dup; apply dict_add_with_no_dup; auto.
  Qed.

  Definition sd_count d k := match dict_get d k with Some n => n | None => 0 end.

  Lemma sd_count_cons : forall d k v, sd_count (dcons k v d) k = v.
  Proof. unfold sd_count. x_ind d; simpl. Qed.

  Lemma sd_count_cons_neq : forall d k k' v, k <> k' -> sd_count (dcons k v d) k' = sd_count d k'.
  Proof. unfold sd_count. x_ind d; simpl. Qed.

  Lemma sd_count_none : forall d k, ~ dict_in k d -> sd_count d k = 0.
  Proof.
    unfold sd_count.
    x_ind d; simpl. apply IHd in H. dest_match; auto. 
  Qed.

  Lemma sd_count_dict_get : forall d k n, dict_get d k = Some n -> sd_count d k = n.
  Proof.
    unfold sd_count.
    x_ind d; simpl; unfold dict_in in H; simpl in H; firstorder; try congruence.
  Qed. 




  Lemma support_dict_count_helper : forall b k acc n, 
    sd_count (support_dict_fold b acc) k + n = sd_count acc k + support_helper b k n.
  Proof.
    induction b; intros; simpl in *; auto. 
    rewrite IHb. clear IHb. dest_match; induction acc; simpl; 
    unfold sd_count; simpl in *; dest_match; simpl in *; dest_match; try x_inj; auto;
    rewrite support_default; symmetry; rewrite support_default; auto;
    try (eapply dict_add_with_get_some with (default:=1)(f:= fun v => S v) in EQ2;
    rewrite EQ0 in EQ2; x_inj; auto; fail);
    try (eapply dict_add_with_get_none with (default:=1)(f:= fun v => S v) in EQ2;
    rewrite EQ0 in EQ2; x_inj; auto; fail).
    - apply dict_get_none in EQ0. rewrite dict_add_with_in in EQ0. rewrite dict_add_in in EQ0. firstorder. 
    - apply dict_get_none in EQ0. rewrite dict_add_with_in in EQ0. rewrite dict_add_in in EQ0. firstorder.
    - rewrite dict_add_with_not_in in *; auto.
    - rewrite dict_add_with_not_in in *; auto.
    - rewrite dict_add_with_not_in in *; auto.
  Qed. 

  Lemma support_dict_count : forall b k acc n, 
    ~ dict_in k acc ->
    support_helper b k n = n + sd_count (support_dict_fold b acc) k.
  Proof.
    intros. symmetry.  rewrite Nat.add_comm.
    rewrite support_dict_count_helper. 
    apply sd_count_none in H. rewrite H; auto.
  Qed.

  Fixpoint sd_to_b_helper (d : dict T nat) (l : bag T) : bag T :=
    match d with
    | dnil => l
    | dcons k v d => sd_to_b_helper d l ++ (list_mul v k)
    end.

  (* convert a support map to a bag *)
  Definition sd_to_b d : bag T := sd_to_b_helper d [].

  Lemma support_app_helper : forall b1 b2 a n, 
    support_helper (b1 ++ b2) a n = (support_helper b1 a 0) + (support_helper b2 a 0) + n.
  Proof.
    induction b1; simpl; intros; auto; 
    dest_match; try rewrite IHb1 in *; try lia.
    rewrite support_default; auto.  
    symmetry. rewrite support_default. lia. 
  Qed.

  Lemma support_app : forall b1 b2 a, 
    support (b1 ++ b2) a = support b1 a + support b2 a.
  Proof.
    unfold support; intros.
    rewrite support_app_helper; auto.
  Qed.
  
  Lemma support_mul : forall a n n',
    support_helper (list_mul n a) a n' = n' + n.
  Proof.
    induction n; intros; rewrite support_default; simpl; auto.
    rewrite IHn. dest_match; auto.
  Qed. 

  Lemma support_mul_neq : forall a a' n n',
    a <> a' -> support_helper (list_mul n a) a' n' = n'.
  Proof.
    induction n; intros; rewrite support_default; simpl; auto.
    rewrite IHn. dest_match; auto. auto.
  Qed. 

  Lemma support_helper_conv : forall d l k n,
    dict_no_dup d ->
    support_helper (sd_to_b_helper d l) k n = 
    support_helper l k n + sd_count d k.
  Proof.
    unfold sd_count.
    x_ind d; rewrite support_default in *; 
    symmetry; rewrite support_default;
    simpl; try x_inj;
    inversion H; subst; apply nodup_dcons in H; rewrite support_app_helper; try rewrite support_mul;
    try rewrite support_mul_neq; auto; rewrite IHd; dest_match; auto.
    - apply dict_get_some in EQ. rewrite dict_in_keys in EQ. auto. 
    - x_inj; auto.
  Qed.

  Lemma support_dict_in_acc : forall b acc k , dict_in k acc -> dict_in k (support_dict_fold b acc).
  Proof.
    x_ind b. apply IHb. rewrite dict_add_with_in. 
    rewrite dict_add_in. auto.
  Qed.

  Lemma support_dict_in : forall b acc k , List.In k b -> dict_in k (support_dict_fold b acc).
  Proof.
    x_ind b. destruct H; subst. 
    - apply support_dict_in_acc. rewrite dict_add_with_in; rewrite dict_add_in; auto.
    - apply IHb. auto.
  Qed.


  Lemma dict_in_support_fold_helper : forall x k acc, 
    dict_in k (support_dict_fold x acc) <-> In k x \/ dict_in k acc.
  Proof.
    x_ind x; split; intros; auto. destruct H; auto.
    apply IHx in H. destruct H; auto. 
    apply dict_add_with_in in H. rewrite dict_add_in in H. destruct H; auto.
    destruct H; try destruct H; subst. 
    - rewrite IHx. right. rewrite dict_add_with_in; rewrite dict_add_in; auto.
    - rewrite IHx. auto.
    - rewrite IHx. right. rewrite dict_add_with_in; rewrite dict_add_in; auto.
  Qed.

  Lemma dict_in_support_fold : forall x k, 
    dict_in k (support_dict_fold x dnil) -> In k x.
  Proof.
    intros. rewrite dict_in_support_fold_helper in H. destruct H; 
    unfold dict_in in *; simpl in H; auto.
  Qed.
  
  Definition subseteq (b1 b2 : bag T) : Prop := forall x, support b1 x <= support b2 x.

  Lemma support_mono : forall b1 b2 a, subseteq b1 b2 -> support b1 a <= support b2 a.
  Proof.
    unfold subseteq. unfold support.
    induction b1; intros; simpl; auto.
    dest_match; simpl in *; auto; [specialize (H a) | specialize (H a0)]; dest_match; auto;
    apply IHb1; intros.
  Qed.

  Lemma support_in_pos : forall b x,
    In x b <-> support b x > 0.
  Proof.
    x_ind b; split; simpl; intros; auto.
    - rewrite support_nil in H; auto.
    - rewrite support_cons; firstorder; dest_match; auto.
    - rewrite support_cons in H; dest_match; auto. right. 
      rewrite IHb. auto.
  Qed.

  Lemma support_not_in_zero : forall b x,
    ~In x b <-> support b x = 0.
  Proof.
    x_ind b; try rewrite support_cons; firstorder; dest_match; firstorder.
    unfold "~"; intros. firstorder. 
    assert (support b x = 0). auto.
    firstorder. 
  Qed.
End BagSupport.

Ltac bag_rew := let H := fresh "H" in
repeat match goal with
| [H : context [support (_ :: _) _] |- _] => 
  rewrite support_cons in H; dest_match
| [|- context [support (_ :: _) _]] => rewrite support_cons; dest_match
| [H : context [support [] _] |- _] => 
  rewrite support_nil in H; dest_match
| [|- context [support [] _]] => rewrite support_nil; dest_match
end.
Section BagMap.
  Variable A B : Type.
  Context `{EqDec A, EqDec B}.
  Variable f : A -> B.
  Definition bag_map (b : bag A) : bag B := List.map f b.

  Lemma bag_map_app : forall a b,
    bag_map (a ++ b) = bag_map a ++ bag_map b.
  Proof.
    induction a; intros; simpl; auto.
  Qed.

  Lemma support_map : forall b x y, 
    (forall a b, a <> b -> f a <> f b) ->
    y = f x ->
    support (bag_map b) y = support b x.
  Proof.
    x_ind b; bag_rew; erewrite IHb; eauto.
    specialize (H1 a x n). auto.
  Qed.

  Lemma support_map_elem_mono : forall b x, 
    support b x <= support (bag_map b) (f x).
  Proof.
    induction b; simpl; intros; subst; bag_rew; auto;
    specialize (IHb x) as [| ?]; auto.
  Qed.

  Lemma support_map_case : forall a y,
    support (bag_map a) y > 0 -> 
    exists x, f x = y /\ support a x > 0.
  Proof.
    intros. induction a; simpl in *.
    - x_inv H1.
    - rewrite support_cons in H1. dest_match.
      + exists a. firstorder. rewrite support_cons. dest_match; auto.
      + rewrite Nat.add_0_r in H1. apply IHa in H1.
        destruct H1 as [x [H1 H2]].
        exists x. firstorder. rewrite support_cons. dest_match; auto.
  Qed.

End BagMap.




(* Arguments support {T EqT}.
Arguments support_helper {T EqT}.
Arguments support_dict {T EqT}.
Arguments support_dict {T EqT}.
Arguments subseteq {T EqT}. *)

Notation "{ }" := empty_bag (format "{ }") : bag_scope.

Notation "{ b }" := (singleton b) : bag_scope.

Notation " b1 ⊆ b2 " := (subseteq b1 b2) (at level 50) : bag_scope.

#[global, refine] Instance bag_Setoid T `{EqDec T} : Setoid (bag T) := {|
  equiv b1 b2 := forall b, support b1 b = support b2 b
|}.
Proof. 
  all: auto.
  constructor; try firstorder.
Defined. 


Section BagSubset.
  Variable T : Type.
  Context `{EqT : EqDec T}.

  Implicit Type x : bag T.
  (* TODO: use a partial order to describe .*)
  Lemma subseteq_trans : forall x y z, 
    x ⊆ y -> y ⊆ z -> x ⊆ z.
  Proof.
    unfold subseteq.
    intros. specialize (H0 x0). specialize (H x0). lia. 
  Qed. 

  Lemma subseteq_refl : forall x, subseteq x x.
  Proof. unfold subseteq. intros. lia. Qed.

End BagSubset.

(* Relational operators 
  - union (✓), 
  - difference (✓), 
  - select (✓), 
  - product (✓),
  - equi-join (✓),
  - projection (x), 
  - rename (x)
*)

Section ListDel.
  Variable A : Type.
  Context `{EqDec A}.
  Fixpoint list_del (l : list A) (a : A) : list A :=
    match l with
    | [] => []
    | cons hd l => if eq_dec hd a then l else cons hd (list_del l a)
    end.

  Lemma in_list_del : forall l k a, In k (list_del l a) -> In k l.
  Proof. x_ind l; simpl in *; firstorder. Qed.

  Lemma support_list_del_same : forall l a,
    support (list_del l a) a = support l a - 1.
  Proof. x_ind l; bag_rew; auto. rewrite IHl; auto. Qed.

  Lemma support_list_del_diff : forall l a k,
    k <> a -> support (list_del l a) k = support l k.
  Proof. x_ind l; bag_rew; auto. Qed.

  Variable A1 : Type.
  Context `{EA1 : EqDec A1}.
  Implicit Type f : A -> A1.
  Lemma map_support_list_del_in : forall b f a,
    In a b ->
    support (bag_map f (list_del b a)) (f a) = 
    support (bag_map f b) (f a) - 1.
  Proof.
    x_ind b; simpl; bag_rew; rewrite ?IHb; firstorder.
    assert (support b a0 <= support (bag_map f b) (f a0)).
      eapply support_map_elem_mono.
    assert (support b a0 > 0).
      apply support_in_pos; auto.
    auto.
  Qed.

  Lemma map_support_list_del_not_in : forall b f a,
    ~In a b ->
    support (bag_map f (list_del b a)) (f a) = 
    support (bag_map f b) (f a).
  Proof. x_ind b; simpl; bag_rew; firstorder. Qed.

  Lemma map_support_list_del_neq : forall b f a1 a2,
    f a1 <> a2 ->
    support (bag_map f (list_del b a1)) a2 = 
    support (bag_map f b) a2.
  Proof. x_ind b; simpl; bag_rew; firstorder. Qed.

  Lemma support_map_mono : forall a b y f,
    (forall x, support a x <= support b x) ->
    support (bag_map f a) y <= support (bag_map f b) y.
  Proof.
    x_ind a; rewrite ?support_nil, ?support_cons; auto; dest_match.
    - specialize (IHa (list_del b a) (f a) f) as Hl.
      assert (forall x : A, support a0 x <= support (list_del b a) x). 
      {
        intros. 
        destruct (eq_dec x a); subst.
        - rewrite support_list_del_same.
          specialize (H0 a); bag_rew; auto.
        - rewrite support_list_del_diff; auto.
          specialize (H0 x); bag_rew; auto.
      }
      assert (support b a > 0).
      { specialize (H0 a); bag_rew; auto. }
      assert (In a b).
      { rewrite support_in_pos; auto. exact H2. }
      assert (support (bag_map f b) (f a) > 0).
      {
        pose proof support_map_elem_mono.
        assert (forall x y, x <= y -> x > 0 -> y > 0).
        lia.
        eapply H5; eauto.        
      }
      eapply Hl in H1.
      rewrite map_support_list_del_in in H1; auto.
    - assert (Heq: support (bag_map f a0) y + 0 = support (bag_map f a0) y). {auto. }
      rewrite Heq; clear Heq.
      eapply IHa.
      intros.
      destruct (eq_dec x a); subst; [specialize (H0 a) | specialize (H0 x)]; 
      bag_rew; auto. 
  Qed.

End ListDel.

Section BagDiff.  
  Variable T : Type.
  Context `{EqT : EqDec T}.
  

  (* Since fold_right is easier to reason about, fold_left is more efficient, 
  and we have fold_right g (rev l) = fold_left f l if g x y = f y x, 
  we use the following helper function to .
  *)
  (* Implicit Type b : bag T. *)
  Implicit Types x y : bag T.
  (* Implicit Type dx dy d_acc: dict T nat. *)

  Fixpoint diff_bag x y : bag T :=
    match y with
    | [] => x
    | hd :: tl => diff_bag (list_del x hd) tl
    end. 
  Hint Extern 4 => unfold dict_no_dup; simpl : core.
  Hint Extern 4 => constructor : core.

  Lemma support_diff_same : forall b a,
    support (list_del b a) a = support b a - 1.
  Proof.
    x_ind b; rewrite !support_cons, ?IHb; dest_match; auto.
  Qed.

  Lemma support_diff_diff : forall b a k,
    k <> a ->
    support (list_del b k) a  = support b a.
  Proof.
    x_ind b; rewrite !support_cons, ?IHb; dest_match; auto.
  Qed.


  Theorem support_diff : forall y x k, support (diff_bag x y) k = (support x k) - (support y k).
  Proof.
    x_ind y.
    - unfold support. auto. 
    - rewrite IHy. destruct (eq_dec k a); subst.
      + rewrite support_diff_same. rewrite support_cons. dest_match; auto.
      + rewrite support_cons. dest_match; auto. rewrite support_diff_diff; auto.
  Qed. 

  Lemma diff_support_d : forall (b1 b2 b3 : bag T) k, 
    b3 ⊆ b1 -> support (diff_bag (b1 ++ b2) b3) k = support ((diff_bag b1 b3) ++ b2) k.
  Proof.
    intros. 
    repeat (rewrite !support_diff, !support_app).
    rewrite support_diff.
    apply support_mono with (a:=k) in H. auto.
  Qed.

  Lemma in_diff : forall y x k, In k (diff_bag x y) -> In k x.
  Proof.
    x_ind y. 
    apply IHy in H. apply in_list_del in H; auto.
  Qed. 

  Lemma nil_diff : forall b, diff_bag nil b = nil.
  Proof. induction b; simpl; auto. Qed.
  Lemma count_occ_support : forall (b : bag T) n,
    support b n = count_occ eq_dec b n.
  Proof.
    induction b; simpl; intros. auto. 
    dest_match; rewrite support_cons, IHb; dest_match; auto. 
  Qed.

  Lemma support_map_diff : forall T1 `{EqDec T1} b2 b1 (f : T -> T1) a,
    b2 ⊆ b1 ->
    support (bag_map f (diff_bag b1 b2)) a = 
    support (bag_map f b1) a - support (bag_map f b2) a.
  Proof.
    x_ind b2; simpl.
    rewrite support_nil; auto.
    rewrite support_cons; dest_match.
    - pose proof (@List.in_dec T EqT a b1) as [H1 | H2].
      + rewrite IHb2, map_support_list_del_in; auto.
        unfold "⊆" in *; intros.
        destruct (eq_dec x a); subst.
        * specialize (H0 a).
          rewrite support_diff_same. 
          rewrite support_cons in H0.
          dest_eq_dec. auto.
        * rewrite support_diff_diff; auto.
          specialize (H0 x).
          rewrite support_cons in H0.
          dest_match; auto.
      + unfold "⊆" in H; intros.
        specialize (H0 a).
        rewrite support_cons in H0; dest_match; auto.
        eapply support_not_in_zero in H2. 
        rewrite H2 in H0. auto.
    - assert (b2 ⊆ (list_del b1 a)).
      {
        unfold subseteq in *. intros.
        destruct (eq_dec x a); subst;
        [rewrite support_list_del_same ; specialize (H0 a) | rewrite support_list_del_diff; specialize (H0 x)]; auto;
        rewrite support_cons in H0; dest_match; auto.
      }
      rewrite IHb2, map_support_list_del_neq; auto.
  Qed.



End BagDiff.

Notation " b1 // b2 " := (diff_bag b1 b2) (at level 40) : bag_scope.

Arguments diff_bag {_ _}.


Section BagSelection.
  Variable T : Type.
  Context `{EqT : EqDec T}.
  Variable f : T -> bool.
  
  Fixpoint select (b : bag T) : bag T := 
    match b with
    | [] => []
    | hd :: tl => if f hd then hd :: (select tl) else select tl
    end.

  Hint Extern 4 => rewrite !support_default_S in *; auto 1 : core.

  Lemma select_support_true : forall b a, 
    f a = true -> support (select b) a = support b a.
  Proof.
    unfold support.
    x_ind b; simpl; dest_match; auto.
  Qed.

  Lemma select_support_false : forall b a, 
    f a = false -> support (select b) a = 0.
  Proof.
    unfold support.
    x_ind b; simpl; dest_match; auto.
  Qed.

  Lemma select_equiv : forall b1 b2, 
    b1 == b2 -> select b1 == select b2.
  Proof.
    unfold equiv. simpl. 
    intros. 
    assert (f b = true \/ f b = false).
      destruct (f b); auto.
    destruct H0.
    rewrite !select_support_true; auto.
    rewrite !select_support_false; auto.
  Qed.

  Lemma select_mono : forall b1 b2, 
    b1 ⊆ b2 -> select b1 ⊆ select b2.
  Proof.
    unfold subseteq. 
    intros. 
    assert (f x = true \/ f x = false).
      destruct (f x); auto.
    destruct H0.
    rewrite !select_support_true; auto.
    rewrite !select_support_false; auto.
  Qed.

  Lemma select_app : forall b1 b2,
    select (b1 ++ b2) == select b1 ++ select b2.
  Proof.
    unfold equiv. simpl. intros.
    rewrite support_app.
    assert (f b = true \/ f b = false).
      destruct (f _); auto.
    destruct H.
    rewrite !select_support_true; try rewrite support_app; auto.
    rewrite !select_support_false; try rewrite support_app; auto.
  Qed.

  Lemma select_diff : forall b1 b2,
    select (diff_bag b1 b2) == diff_bag (select b1) (select b2).
  Proof.
    unfold equiv. simpl. intros.
    rewrite support_diff.
    assert (f b = true \/ f b = false).
      destruct (f _); auto.
    destruct H.
    rewrite !select_support_true; try rewrite support_diff; auto.
    rewrite !select_support_false; try rewrite support_diff; auto.
  Qed.


End BagSelection.


Section BagUnionAll.
  Variable T : Type.
  Context `{EqT : EqDec T}.

  Definition union_all b1 b2 : bag T := b1 ++ b2.

  Lemma support_union_d : forall b1 b2 a, 
    support (union_all b1 b2) a = (support b1 a) + (support b2 a).
  Proof.
    unfold union_all. unfold support.  
    induction b1; simpl; intros; auto; 
    dest_match; try rewrite IHb1 in *; try lia.
    rewrite support_default. rewrite IHb1. simpl. 
    symmetry. rewrite support_default. auto.
  Qed. 

  Lemma union_all_comm : forall b1 b2 a, 
    support (union_all b1 b2) a = support (union_all b2 b1) a.
  Proof.
    unfold union_all. intros. rewrite !support_union_d; lia. 
  Qed.

  Lemma union_all_ss_left : forall b1 b2, b1 ⊆ union_all b1 b2.
  Proof. 
    intros. unfold subseteq; unfold union_all; intros. rewrite support_app. lia. 
  Qed.

  Lemma union_all_ss_right : forall b1 b2, b1 ⊆ union_all b2 b1.
  Proof. 
    intros. unfold subseteq; unfold union_all; intros. rewrite support_app. lia. 
  Qed.



  Lemma union_all_setoid : forall b b1 b2, b1 == b2 -> b ⊆ b1 -> b ⊆ b2. 
  Proof.
    unfold equiv. unfold subseteq. simpl. intros. 
    specialize (H x); specialize (H0 x); auto.
  Qed.
  

End BagUnionAll.

Notation "b1 ⊎ b2" := (union_all b1 b2) (at level 50) : bag_scope.


Section BagProduct.
  (* cartesian product *)
  Variable T1 T2 : Type.
  Context `{EqT1 : EqDec T1, EqT2 : EqDec T2}.  

  Fixpoint product (b1 : bag T1) (b2 : bag T2) : bag (T1 * T2) := 
    match b1 with
    | [] => []
    | hd :: tl => (map (fun x => (hd, x)) b2) ++ (product tl b2)
    end.
  
  Notation "b1 ⋅ b2" := (product b1 b2)(at level 20). 

  Lemma support_prod_map : forall b (a : T1) y n, 
    support_helper (map (fun x => (a, x)) b) (a, y) n = 
      support_helper b y n.
  Proof. x_ind b. Qed.  
  
  Lemma support_prod : forall b1 b2 x y,
    support (b1 ⋅ b2) (x, y) = (support b1 x) * (support b2 y).
  Proof.
    unfold support.
    x_ind b1; simpl in *; try nia.
    - rewrite support_app_helper; simpl.
      rewrite IHb1.
      rewrite support_default_S. 
      rewrite support_prod_map with (n:=0)(y:=y)(a:=a).
      lia.
    - rewrite support_app_helper; simpl.
      rewrite IHb1.
      assert (support_helper (map (fun x0 : T2 => (a, x0)) b2) (x, y) 0 = 0).
        x_ind b2.
      rewrite H. lia.
  Qed.
  
  Lemma product_mono_left : forall b1 b2 b3, b1 ⊆ b2 -> product b1 b3 ⊆ product b2 b3.
  Proof.
    unfold subseteq. intros.
    destruct x. rewrite !support_prod. 
    specialize (H t). nia.
  Qed.

  Lemma product_mono_right : forall b1 b2 b3, b1 ⊆ b2 -> product b3 b1 ⊆ product b3 b2.
  Proof.
    unfold subseteq. intros.
    destruct x. rewrite !support_prod. 
    specialize (H t0). nia.
  Qed.

End BagProduct.

Notation "b1 ⋅ b2" := (product b1 b2) (at level 40) : bag_scope.

Ltac bag_support := repeat match goal with
| [|- context[support (_ ++ _) _]] => rewrite support_union_d
| [|- context[support (_ ⊎ _) _]] => rewrite support_union_d
| [|- context[support (_ ⋅ _) _]] => rewrite support_prod
| [|- context[support (_ :: _) _]] => rewrite support_cons
| [|- context[support [] _]] => rewrite support_nil
end.



Module EquiJoin.
  
  Section JoinIndex.
    Variables K T : Type.
    Context `{EqK : EqDec K, EqT : EqDec T}.
    Definition join_ix := dict K (bag T). 
    Fixpoint ix_support (d : join_ix) (k : K) (x : T) :=
      match d with 
      | dnil => 0
      | dcons k' b d => if eq_dec k' k then support b x else ix_support d k x
      end.

    Variable c : T -> K.

    Definition valid_ix k b := forall x, In x b -> c x = k.
    Inductive join_ix_inv : join_ix -> Prop :=
    | join_ix_nil : join_ix_inv dnil
    | join_ix_cons k b d : join_ix_inv d ->
                           valid_ix k b ->
                           ~ dict_in k d ->
                           join_ix_inv (dcons k b d)
    .
    
    
    Hint Extern 4 => constructor : core.

    Lemma join_ix_inv_cons : forall d k v,
      join_ix_inv (dcons k v d) -> join_ix_inv d.
    Proof.
      intros. inversion H; subst. auto.
    Qed.

    Fixpoint ix_to_bag (d : join_ix) : bag T :=
      match d with
      | dnil => []
      | dcons k v d => v ++ (ix_to_bag d)
      end.


    Fixpoint ix_diff_elem (d : join_ix) (t : T) : join_ix :=
      match d with
      | dnil => dnil
      | dcons k v d => if eq_dec k (c t) then dcons k (list_del v t) d
                       else dcons k v (ix_diff_elem d t)
      end.

    Lemma dict_in_ix_diff_elem : forall d t k,
      dict_in k (ix_diff_elem d t) -> dict_in k d.
    Proof.
      x_ind d; simpl in *; dest_match; eauto.
      Unshelve. all: auto. 
    Qed.

    Lemma diff_ix_elem_prop : forall d t,
      join_ix_inv d -> join_ix_inv (ix_diff_elem d t).
    Proof.
      x_ind d; simpl; inversion H; subst; try constructor;
      unfold valid_ix in *; intros; eauto.
      eapply H4. eapply in_list_del; eauto. 
      unfold "~". intros. apply dict_in_ix_diff_elem in H0. auto.
    Qed.

    Hint Resolve dict_in_ix_diff_elem diff_ix_elem_prop : core.
  
    Definition ix_diff_bag (d : join_ix) (b : bag T) : join_ix :=
      fold_left ix_diff_elem b d.


    Lemma dict_in_ix_diff : forall d b k,
      dict_in k (ix_diff_bag d b) -> dict_in k d.
    Proof.
      unfold ix_diff_bag. 
      intros d b k.
      apply fold_left_ind; intros; subst; simpl in *; eauto.
    Qed.

    Lemma diff_ix_prop : forall d b,
      join_ix_inv d ->
      join_ix_inv (ix_diff_bag d b).
    Proof.
      unfold ix_diff_bag. intros. eapply fold_left_ind; intros; subst; simpl in *; auto.
    Qed.

  End JoinIndex.

  (*
  build_ix c2 (b0 ⊎ b2) = build_ix_helper c2 b2 (build_ix c2 b0)
  build_ix c2 (BagDiff.diff_bag b0 b2) = ix_diff_bag (build_ix c2 b0) b2

  *)
  Section EquiJoin.
  
    Section EquiJoinStep1.
    
      Variables A K : Type.
      Context `{EqA : EqDec A, EqK : EqDec K}.
      Variable c : A -> K.
      Implicit Type b : bag A.

      Definition update_ix (d : join_ix K A) (a : A) : join_ix K A :=
        dict_add_with d (c a) [a] (fun x => a :: x). 
        
      Fixpoint ix_get (d : join_ix K A) (k : K) : bag A :=
        match d with
        | dnil => []
        | dcons k' v d => if eq_dec k k' then v else ix_get d k
        end.

      Lemma ix_get_eq : forall d x, support (ix_get d (c x)) x = ix_support d (c x) x.
      Proof.
        x_ind d.
      Qed.

      Lemma ix_get_neq : forall d x y, 
        join_ix_inv c d -> c x <> y -> support (ix_get d y) x = 0.
      Proof.
        x_ind d. 
        inversion H; subst. 
        unfold valid_ix in H5.
        - apply support_not_in. auto.
        - apply IHd; inversion H; auto. 
      Qed.

      Hint Extern 4 => constructor : core.
      Ltac daw_rev := rewrite <- ?dict_in_keys, dict_add_with_in, dict_add_in.

      Lemma update_ix_no_dup : forall d a,
        dict_no_dup d -> dict_no_dup (update_ix d a).
      Proof.
        unfold update_ix.
        unfold dict_no_dup.
        x_ind d; simpl.
        inversion H; subst.
        constructor.
        - daw_rev. rewrite dict_in_keys. firstorder.
        - auto.
      Qed. 

      Lemma update_ix_prop : forall d a, 
        join_ix_inv c d ->
        join_ix_inv c (update_ix d a).
      Proof.
        unfold update_ix.
        x_ind d; constructor; unfold valid_ix; intros; 
        simpl in *; auto; try destruct H0; auto;
        try inversion H; subst; auto.
        daw_rev; firstorder.
      Qed.

      Hint Resolve update_ix_no_dup : core.

      Definition build_ix_helper b init : join_ix K A := 
        fold_left update_ix b init. (* O(length b1) *)
      
      Definition build_ix b := build_ix_helper b dnil.


      Lemma build_ix_no_dup : forall b init,
        dict_no_dup init ->
        dict_no_dup (build_ix_helper b init).
      Proof.
        unfold dict_no_dup. x_ind b.
        unfold build_ix_helper.  
        apply IHb. apply update_ix_no_dup. auto.
      Qed.

      Hint Resolve build_ix_no_dup : core.

      Lemma build_ix_prop : forall b init, 
        join_ix_inv c init ->
        join_ix_inv c (build_ix_helper b init).
      Proof.
        x_ind b.
        apply IHb. unfold update_ix. 
        inversion H; subst; simpl;
        dest_match; constructor; 
        unfold valid_ix; intros;
        simpl in *; auto.
        - destruct H0; subst; auto.
        - destruct H3; subst; auto.
        - apply update_ix_prop; auto.
        - daw_rev; firstorder.
      Qed.

      Hint Extern 4 => unfold support : core.
      Hint Extern 4 => rewrite support_default_S : core.

      Lemma ix_support_update : forall d a,
        ix_support (update_ix d a) (c a) a = 1 + ix_support d (c a) a.
      Proof.
        unfold update_ix.
        x_ind d. cbv; dest_match; auto.
        - repeat (simpl; dest_match; unfold support; auto).
        - simpl. dest_match; auto.
      Qed.

      Lemma ix_support_update_neq : forall d a x,
        x <> a ->
        ix_support (update_ix d a) (c x) x = ix_support d (c x) x.
      Proof.
        unfold update_ix.
        x_ind d. cbv; dest_match; auto.
        - repeat (simpl; dest_match; unfold support; auto).
        - simpl. dest_match; auto.
        - simpl. dest_match; auto.
        - simpl. dest_match; auto.
      Qed.


      Lemma ix_support_build_ix_helper : forall b x init,
        ix_support (build_ix_helper b init) (c x) x = 
        support b x + ix_support init (c x) x.
      Proof.
        unfold support.
        x_ind b; simpl; 
        rewrite ?IHb, ?ix_support_update, ?ix_support_update_neq; auto.
      Qed.
          
      Lemma ix_support_build_ix : forall b x, 
        ix_support (build_ix b) (c x) x = support b x.
      Proof.
        unfold build_ix. unfold support. intros.
        rewrite ix_support_build_ix_helper; simpl; auto.
      Qed.
      Implicit Type d : join_ix K A.

      Lemma ix_support_not_in : forall d x,
        ~ dict_in (c x) d -> ix_support d (c x) x = 0.
      Proof.
        x_ind d.
      Qed.
      Lemma ix_support_diff_ix_elem_eq : forall d a,
        join_ix_inv c d ->
        ix_support (ix_diff_elem c d a) (c a) a =
        ix_support d (c a) a - 1.
      Proof.
        x_ind d; simpl in *; dest_match; auto.
        - rewrite support_diff_same; auto.
        - rewrite IHd; auto. inversion H; subst; auto.
      Qed.

      Lemma ix_support_diff_ix_elem_neq : forall d (a a' : A),
        join_ix_inv c d ->
        a <> a' ->
        ix_support (ix_diff_elem c d a) (c a') a' =
        ix_support d (c a') a'.
      Proof.
        x_ind d; simpl in *; dest_match; auto. 
        - rewrite support_diff_diff; auto.
        - rewrite IHd; eauto. inversion H; subst. auto.
      Qed.

      Lemma ix_support_diff_ix : forall b d k,
        join_ix_inv c d ->
        ix_support (ix_diff_bag c d b) (c k) k =
        ix_support d (c k) k - support b k.
      Proof.
        induction b; intros; simpl.
        - unfold support. simpl. lia.
        - rewrite IHb.
          destruct (eq_dec a k); subst.
          + rewrite ix_support_diff_ix_elem_eq; auto.
            unfold support. simpl.
            dest_eq_dec. auto.
          + rewrite ix_support_diff_ix_elem_neq; auto.
            unfold support. simpl. dest_eq_dec.
          + auto using diff_ix_elem_prop.
      Qed.
      Lemma ix_support_cons_eq : forall d x v,
        join_ix_inv c (dcons (c x) v d) ->
        ix_support (dcons (c x) v d) (c x) x = support v x.
      Proof.
        x_ind d.
      Qed.

      Lemma ix_support_cons_neq : forall d k x v,
        join_ix_inv c (dcons k v d) ->
        k <> c x -> 
        ix_support (dcons k v d) (c x) x = ix_support d (c x) x.
      Proof.
        x_ind d.
      Qed.

      Lemma support_neq_key_zero : forall d k v x, 
        join_ix_inv c (dcons k v d) ->
        k <> c x ->
        support v x = 0.
      Proof.
        x_ind d; inversion H; subst; auto;
        unfold valid_ix in H5;
        apply support_not_in; firstorder.
      Qed.

      Hint Resolve nodup_dcons : core.
      Hint Extern 4 => rewrite <- dict_in_keys : core.

      Lemma ix_support_in : forall d x,
        join_ix_inv c d ->
        support (ix_to_bag d) x = ix_support d (c x) x.
      Proof.
        x_ind d; inversion H; subst;
        rewrite support_app, IHd; auto 1.
        - rewrite ix_support_not_in; auto.
        - erewrite support_neq_key_zero; eauto.
      Qed. 

      Hint Resolve build_ix_prop : core.
      
      Lemma ix_to_bag_equiv : forall b x,
        support (ix_to_bag (build_ix b)) x = support b x.
      Proof.
        intros.
        rewrite ix_support_in.
        rewrite ix_support_build_ix; auto.
        apply build_ix_prop; auto.
      Qed.

      Lemma ix_support_equiv : forall b x,
        ix_support (build_ix b) (c x) x = support b x.
      Proof.
        intros.
        rewrite <- ix_support_in; auto.
        apply ix_to_bag_equiv.
        apply build_ix_prop; auto.
      Qed.

      Lemma ix_support_app_helper : forall b1 b2 k init,
        ix_support (build_ix_helper (b1 ⊎ b2) init) (c k) k =
          ix_support init (c k) k +
          ix_support (build_ix b1) (c k) k +
          ix_support (build_ix b2) (c k) k.
      Proof.
        unfold build_ix. x_ind b1;
        rewrite ix_support_build_ix_helper.
        - rewrite <- ix_support_equiv. unfold build_ix. auto.
        - rewrite support_app.
          assert (forall a, support b2 a = ix_support (build_ix_helper b2 dnil) (c a) a).
            intros; rewrite <- ix_support_equiv; auto.
          destruct (eq_dec k a); subst;
          [rewrite ix_support_update | rewrite ix_support_update_neq]; auto.
          + rewrite ix_support_build_ix_helper, ix_support_update, 
                    <- ix_support_equiv, H; simpl; auto.
          + rewrite ix_support_build_ix_helper, ix_support_update_neq, H; simpl; auto.
      Qed.

      Lemma ix_support_app : forall b1 b2 k,
        ix_support (build_ix (b1 ⊎ b2)) (c k) k =
          ix_support (build_ix b1) (c k) k +
          ix_support (build_ix b2) (c k) k.
      Proof.
        intros. unfold build_ix. rewrite ix_support_app_helper; auto.
      Qed.


      Lemma ix_support_diff_helper : forall b2 b1 k init,
        ix_support (build_ix_helper (diff_bag b1 b2) init) (c k) k =
          ix_support (build_ix b1) (c k) k -
          ix_support (build_ix b2) (c k) k +
          ix_support init (c k) k
          .
      Proof.
        x_ind b2.
        - rewrite ix_support_build_ix_helper, ix_support_equiv. auto.
        - unfold build_ix. 
          rewrite !ix_support_build_ix_helper, support_cons, support_diff.
          dest_match; simpl.
          + rewrite support_list_del_same. lia.
          + rewrite support_list_del_diff; auto.
      Qed. 
          
    Lemma ix_support_diff : forall b1 b2 k,
      ix_support (build_ix (diff_bag b1 b2)) (c k) k =
        ix_support (build_ix b1) (c k) k -
        ix_support (build_ix b2) (c k) k.
    Proof.
      intros. 
      rewrite !ix_support_equiv.
      rewrite support_diff; auto.
    Qed.

        
    End EquiJoinStep1.

    Section EquiJoinStep2.
      Variables A B K : Type.
      Context `{EqA : EqDec A, EqB : EqDec B, EqK : EqDec K}.
      Fixpoint match_ix (c : B -> K) (b : bag B) (ix : join_ix K A) : bag (A * B) :=
        match b with
        | [] => []
        | hd :: b => ((ix_get ix (c hd)) ⋅ [hd]) ++ match_ix c b ix     
        end.

      Lemma match_build_ix_support : forall c1 c2 b d x y, 
        c1 x = c2 y ->
        support (match_ix c2 b d) (x, y) = (ix_support d (c1 x) x) * (support b y).
      Proof.
        x_ind b.
        rewrite support_app, support_prod, !support_cons, IHb; simpl; auto.
        dest_match.
        - rewrite <- H, ix_get_eq; nia.
        - nia.
      Qed.  

      Lemma match_build_ix_support_0 : forall c1 c2 b d x y, 
        join_ix_inv c1 d ->
        c1 x <> c2 y ->
        support (match_ix c2 b d) (x, y) = 0.
      Proof.
        x_ind b.
        rewrite support_app, support_prod, !support_cons, IHb; simpl; auto.
        dest_match.
        - erewrite Nat.mul_1_r, Nat.add_0_r, ix_get_neq; eauto. 
        - nia.
      Qed.

    End EquiJoinStep2.

    Definition equi_join {A B K} `{EqDec K} 
          (c1 : A -> K) (c2 : B -> K) 
          (b1 : bag A) (b2 : bag B) : bag (A * B) := 
      match_ix c2 b2 (build_ix c1 b1).

          
  End EquiJoin.

End EquiJoin.
