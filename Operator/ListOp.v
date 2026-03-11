(* From Stdlib Require Import List Lia Compare_dec PeanoNat Eqdep_dec Compare_dec FunctionalExtensionality.
From AUTOINC Require Import EqDec Change ListChange NatChange Tactic Operator.
From AUTOINC Require Import AggregateTree.
Import ListNotations.

Hint Extern 4 => apply nat_EqDec : core.
Hint Extern 4 => apply list_change_EqDec : core.
Hint Extern 4 => lia : core.

Module LengthInc <: StatelessDiffOp.
  Definition T1   := list nat.
  Definition T2   := nat.
  Definition EqT1 := @list_EqDec nat nat_EqDec.
  Definition EqT2 := nat_EqDec.
  Definition C1   := listc nat.
  Definition C2   := natc.

  Definition f (l: T1) : T2 := List.length l.

  Definition Δf (c : C1.(ΔT)) : C2.(ΔT)  :=
    match c with
    | list_noc => nat_add 0
    | list_insert i _ => nat_add 1
    | list_delete i _ => nat_minus 1
    end.

  Hint Constructors list_change : core.
  Hint Extern 4 => econstructor : core. 
  Hint Extern 4 => unfold f : core.
  Hint Extern 4 => unfold Δf : core.
  Hint Extern 4 => lia : core.
  
  Lemma inc_valid : forall x Δx,
    vc Δx x -> vc (Δf Δx) (f x).
  Proof.
    intros x Δx H2.
    inversion H2; subst; auto.
  Qed.

  Lemma inc_correct_insert : forall l i a vc,
    f (insert_patch nat l i a vc) = S (f l).
  Proof.
    induction l; intros.
    - simpl in vc. assert (i = 0). lia. subst. simpl. auto.
    - simpl in vc. simpl. destruct i; simpl. auto. rewrite IHl. auto.
  Qed. 

  Lemma inc_correct_delete : forall l i H,
    f (delete_patch l i H) = (f l) - 1.
  Proof.
    induction l; intros; simpl in *; try lia. destruct i. lia. simpl.
    rewrite IHl; auto. 
  Qed.

  Hint Extern 4 => rewrite inc_correct_insert : core.
  Hint Extern 4 => rewrite inc_correct_delete : core.

  Lemma inc_correct : forall x Δx vcx vcy,
    f (patch Δx x vcx) = patch (Δf Δx) (f x) vcy.
  Proof.
    intros x Δx vcx vcy; simpl in *. unfold Δf.
    dest_patch vcx list_vc_case; auto 2.
    - simpl. auto. 
    - simpl. auto.
  Qed.
End LengthInc.


Module MaxInnatc : SFInOutOP.
  Definition T1 := list nat.
  Definition T2 := nat.
  Definition C1 := listc nat.
  Definition C2 := natc.

  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).

  Implicit Type t : T1.
  Implicit Type Δt : ΔT1.

  Definition f := list_max. 
  Notation vci := (@vc T1 C1).

  Program Definition Δf Δt i o (_ : vci Δt i) : ΔT2 :=
    match Δt with
    | list_noc => nat_add 0
    | list_insert _ x =>
      if le_dec x (f i) then nat_add 0 else nat_repl o x
    | list_delete k x =>
      if lt_dec x o then nat_add 0 else nat_repl o (f (delete_patch i k _))
    end.
  Next Obligation. inversion v; auto. Defined.


  (* Note : the following function will lead to a bug in Coq :(. 
  But we can avoid it once we substitute `list_patch (list_delete i) l _` with
  `delete_patch l i _`.
  *)
  (* Program Definition Δf1 Δt st (vst : vs Δt st) : ΔT2 := 
  match Δt with
  | list_noc => nat_noc
  | list_repl l l' => nat_repl (f l) (f l')
  | list_insert i x =>
    let '(l, m) := st in
    if le_dec x m then nat_noc else nat_repl m x
  | list_delete i =>
    let '(l, m) := st in
    let x := nth_safe nat l i _ in
    if lt_dec x m then nat_noc else nat_repl m (f (list_patch (list_delete i) l _))
  end.
  Next Obligation.
    inversion vst; auto.
  Defined.
  Next Obligation.
    inversion vst; auto.
  Defined. *)
  

  Global Transparent Δf f.
  Hint Extern 4 => unfold f : core.
  Hint Extern 4 => unfold Δf : core.

  Hint Extern 4 => apply nat_vc_repl : core.
  Hint Extern 4 => constructor : core.

  Lemma inc_valid : forall Δx i o vsx, Δf Δx i o vsx ↪ o.
  Proof.
    simpl. unfold T1. unfold f. intros.
    inversion vsx; subst; simpl; try constructor; dest_match; auto. 
  Qed.  

  Lemma inv_step_insert : forall l i a H,
    f (insert_patch nat l i a H) = Nat.max a (f l).
  Proof.
    induction l; intros.
    - simpl in *. destruct i; simpl; auto.
    - simpl in H. destruct i. 
      + simpl. lia.
      + simpl. rewrite IHl. lia.
  Qed.


  Lemma delete_patch_le : forall l i H, f (delete_patch l i H) <= f l.
  Proof.
    induction l; intros.
    - simpl in *. destruct i; simpl; auto.
    - simpl in H. destruct i. 
      + simpl. lia.
      + eapply PeanoNat.lt_S_n in H as H1. specialize (IHl i H1).
        simpl. rewrite delete_patch_pir with (H2:=H1). lia.
  Qed.

  Lemma inv_step_delete : forall l i H,
    nth_safe nat l i H < f l ->
    f (delete_patch l i H) = f l.
  Proof.
    induction l; intros; auto 2.
    - simpl in *. auto.
    - destruct i. simpl in *. auto. 
      simpl in H. eapply PeanoNat.lt_S_n in H as H1.
      simpl in H0.
      rewrite nth_th with (H2:=H1) in H0.
      simpl in H0.
      simpl. rewrite delete_patch_pir with (H2:=H1).
      assert (H2 : a < f l \/ a >= f l). lia. 
      destruct H2; simpl.
      + rewrite IHl; auto.
      + assert (H3 : Init.Nat.max a (f l) = a).
          auto.
        rewrite H3. 
        pose proof (delete_patch_le l i H1).
        lia.
  Qed.

  Hint Extern 4 => rewrite nat_patch_repl : core.
  Hint Extern 4 => rewrite inv_step_insert : core.


  Lemma inc_correct : forall Δx i vcx vsx vcy, 
    f (i ⊕ Δx ~ vcx) = f i ⊕ Δf Δx i (f i) vsx ~ vcy.
  Proof. 
    intros. unfold f in *. simpl. 
    dest_patch vcx list_vc_case;
    dest_patch vsx list_vc_case; 
    try rewrite <- pf;
    try rewrite <- Eqdep_dec.eq_rect_eq_dec; 
    try apply list_change_EqDec;
    try apply nat_EqDec;
    try congruence; auto 1; simpl; 
    dest_match; simpl;
    try inversion pf; subst;
    try rewrite inv_step_insert;
    try rewrite nat_patch_repl;
    unfold f in *; auto 2. 
    - rewrite inv_step_delete. auto. 
      rewrite nth_th with (H2:=H0). auto.
    - rewrite delete_patch_pir with (H2:=H0). auto.
  Qed.

End MaxInnatc.

Lemma fold_left_ind : forall T1 T2 (f : T1 -> T2 -> T1) 
  (P : T1 -> Prop) init,
  (forall (x:list T2), x = [] -> P (fold_left f x init)) ->
  (forall x t, P t -> P (f t x)) ->
  forall l, P (fold_left f l init).
Proof.
  intros.
  generalize dependent H0.
  generalize dependent init.
  induction l; simpl; intros; auto; simpl.
  specialize (H []). simpl in H. auto.
  apply IHl; auto. intros. subst. simpl. apply H0.
  specialize (H []). simpl in H. auto.
Qed.


Module MaxAggTree 
  (PreOrd : STRICT_PRE_ORDER) 
  (Join : JOIN(PreOrd)) 
  : StatefulDiffOp.

  Module Agg := AggregateTree PreOrd Join.
  Import PreOrd.
  Import Join.
  Import Agg.
  Import Difference.

  Instance eqA : EqDec A := eqa_dec.

  Parameter DiffA : difference A.
  Definition CA := cdiff A DiffA.

  Definition T1 := list A.
  Definition T2 := A.
  Definition C1 := listc A.
  Definition C2 := CA.

  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).

  Implicit Type t : T1.
  Implicit Type Δt : ΔT1.

  Definition f := fold_right join bottom. 
  
  Definition ST : Type := AT.

  Definition inv (l : list A) (st : AT) : Prop :=
    BST st /\ AggT st 
    /\ forall n, count_occ eq_dec l n = count n st
    .
  
  Definition vs (dt1 : ΔT1) (st : ST) : Prop := True.
  
  Definition Δst Δt st (_ : vs Δt st) : ST := 
    match Δt with
    | list_noc => st
    | list_insert _ x => insert x st
    | list_delete _ x => delete x st
    end.
    
  Definition Δf Δt st (H : vs Δt st) : ΔT2 :=
    let st' := Δst Δt st H in
    (result st) ⊖ (result st').

  Definition gen_state (t : T1) := 
    fold_left (fun tree elem => insert elem tree) t Empty.

  Hint Extern 4 => unfold vs : core.
  Hint Extern 4 => unfold inv : core.
  Hint Extern 4 => unfold Δf : core.
  Hint Extern 4 => unfold Δst : core.
    

  Lemma gen_state_count : forall x (t : AT) n,
    BST t ->
    count n (fold_left (fun (tree : AT) (elem : A) => insert elem tree) x t) = 
    count n (fold_left (fun (tree : AT) (elem : A) => insert elem tree) x Empty) +
    count n t.
  Proof.
    induction x; intros; simpl; auto 1.
    rewrite IHx. symmetry. rewrite IHx. simpl.
    dest_match.
    - rewrite count_insert. lia.
    - rewrite count_insert_rest; auto 1.
    - destruct o; subst. congruence.  
      rewrite count_insert_rest; auto.
    - constructor; auto 1. repeat split; try constructor; try lia.
    - apply BST_insert; auto.
  Qed. 

  Lemma gen_state_correct : 
    forall x , inv x (gen_state x).
  Proof. 
    unfold gen_state. 
    intros x; repeat split. 
    - apply fold_left_ind, BST_insert; auto.
    - apply fold_left_ind; intros; subst; try constructor. apply AggT_insert; auto.
    - induction x; intros; simpl; try lia. rewrite IHx. dest_match.
      + rewrite gen_state_count; auto 1.
        symmetry.
        rewrite gen_state_count; simpl. dest_match; try lia; try congruence.
        repeat split; lia.
      + rewrite gen_state_count; auto 1.
        symmetry.
        rewrite gen_state_count; simpl. dest_match; try lia; try congruence.
        repeat split; lia. 
  Qed.
  
  Lemma gen_state_valid : forall t Δt, vc Δt t -> vs Δt (gen_state t).
  Proof. unfold vs. auto. Qed. 

  Lemma state_valid : forall x Δx st,
    inv x st -> Δx ↪ x -> vs Δx st.
  Proof. auto. Qed.

  Lemma count_occ_insert : forall x i a H,
    count_occ eq_dec (insert_patch A x i a H) a = S (count_occ eq_dec x a).
  Proof.
    induction x; intros. 
    - simpl. destruct i; simpl in *; dest_match; auto.
    - simpl in *. destruct i.
      * rewrite count_occ_cons_eq; auto.
      * simpl. dest_match; rewrite IHx; auto.
  Qed.

  Lemma count_occ_insert_rest : forall l i a H x,
    x <> a -> count_occ eq_dec (insert_patch A l i x H) a = count_occ eq_dec l a.
  Proof.
    induction l; intros. 
    - simpl. destruct i; simpl in *; dest_match; auto.
    - simpl in *. destruct i.
      * rewrite count_occ_cons_neq; auto.
      * simpl. dest_match; rewrite IHl; auto.
  Qed.

  Lemma count_occ_nth_pos : forall l i H,
    0 < count_occ eq_dec l (nth_safe A l i H).
  Proof.
    induction l; intros. inversion H.
    simpl in *. dest_match; auto.
  Qed.

  Lemma count_occ_delete : forall x i H,
    count_occ eq_dec (delete_patch x i H) (nth_safe A x i H) 
      = pred (count_occ eq_dec x (nth_safe A x i H)).
  Proof.
    induction x; intros.
    - inversion H.
    - simpl in *. destruct i.
      * dest_match; auto.
      * erewrite nth_th. erewrite delete_patch_pir.
        simpl. dest_match.
        -- rewrite IHx. simpl. rewrite Nat.succ_pred_pos. reflexivity. apply count_occ_nth_pos.
        -- rewrite IHx. reflexivity.
      Unshelve. lia.
  Qed.

  Lemma count_occ_delete_rest : forall x i H a,
    (nth_safe A x i H) <> a -> count_occ eq_dec (delete_patch x i H) a 
      = count_occ eq_dec x a.
  Proof.
    induction x; intros.
    - inversion H.
    - simpl in *. destruct i.
      * dest_match; auto.
      * simpl. dest_match.
        -- erewrite delete_patch_pir. rewrite IHx; auto 3. apply H0.
        -- erewrite delete_patch_pir. rewrite IHx; auto 3. apply H0.
  Qed.

  Lemma inv_step_insert : forall l i a H,
    f (insert_patch A l i a H) = join a (f l).
  Proof.
    induction l; intros.
    - simpl in *. destruct i; simpl; auto. Unshelve. all:auto.
    - simpl in H. destruct i. 
      + auto.
      + simpl. rewrite IHl. rewrite join_assoc. join_comm a a0. join_solve.
  Qed.

  Lemma delete_patch_le : forall l i H, f (delete_patch l i H) <=A f l.
  Proof.
    induction l; intros.
    - simpl in *. destruct i; simpl; auto.
    - simpl in H. destruct i. 
      + simpl. apply join_upper_r.
      + eapply PeanoNat.lt_S_n in H as H1. specialize (IHl i H1).
        simpl. rewrite delete_patch_pir with (H2:=H1). apply join_le; auto.
  Qed.

  Lemma count_occ_filter_pos : forall l f n,
    f n = true -> count_occ eq_dec (filter f l) n = count_occ eq_dec l n.
  Proof.
    induction l; intros. auto.
    simpl. dest_match; auto 2.
    - rewrite count_occ_cons_eq; auto.
    - rewrite count_occ_cons_neq; auto.
  Qed.

  Lemma count_occ_filter_neg : forall l f (n : A),
    f n = false -> count_occ eq_dec (filter f l) n = 0.
  Proof.
    induction l; intros. auto.
    simpl. dest_match; auto 2.
    rewrite count_occ_cons_neq; auto 2.
  Qed.

  Lemma f_filter : forall (l : list A) (g : A -> bool),
    f l = join (f (filter (fun n => g n) l)) (f (filter (fun n => negb (g n)) l)).
  Proof.
    induction l; intros. join_reduce.
    simpl. dest_match; auto 3; simpl.
    - rewrite <- join_assoc. rewrite <- IHl. reflexivity.
    - rewrite join_assoc. join_comm (f (filter (fun n : A => g n) l)) a.
      rewrite <- join_assoc. rewrite <- IHl. reflexivity.
  Qed.

  Lemma filter_nocount : forall l elem,
    count_occ eq_dec l elem = 0 -> filter (fun n => n =?A elem) l = [].
  Proof.
    induction l; intros. auto.
    simpl. dest_match; simpl in *; dest_match; auto 3.
  Qed.

  Lemma f_filter_eq : forall l elem,
    count_occ eq_dec l elem > 0 -> f (filter (fun n => n =?A elem) l) = elem.
  Proof.
    induction l; intros. inversion H.
    simpl. dest_match; lta_solve; simpl. 
    - destruct (count_occ eq_dec l elem) eqn:?.
      * rewrite filter_nocount; join_reduce; auto.
      * rewrite IHl; join_reduce. auto.
    - simpl in *. dest_match; auto 3.
  Qed.

  Lemma filter_compose : forall T (l : list T) f g,
    filter f (filter g l) = filter (fun n => andb (f n) (g n)) l.
  Proof. 
    induction l; intros. auto.
    simpl. dest_match; auto 3; simpl; dest_match; auto 3.
    rewrite IHl. reflexivity.
  Qed.

  Lemma count_result_inv : forall st l,
    inv l st -> f l = result st.
  Proof.
    induction st; intros l [H [H0 H1]].
    - simpl in *. apply count_occ_inv_nil in H1. subst. reflexivity.
    - destruct H as [? [? [? [? ?]]]]. destruct H0 as [? [? ?]]. subst.
      simpl in *. 
      rewrite <- IHst1 with (l := filter (fun n => n <?A elem) l); repeat split; auto 3.
      rewrite <- IHst2 with (l := filter (fun n => elem <?A n) l); repeat split; auto 3.
      * rewrite f_filter with (g := fun n => n =?A elem).
        rewrite f_filter_eq. 2: { rewrite H1. dest_match; auto. }
        rewrite f_filter with (g := fun n => n <?A elem).
        rewrite filter_compose. apply f_equal.
        assert ((fun n => ((n <?A elem) && negb (n =?A elem))%bool) = (fun n => n <?A elem)).
        { apply functional_extensionality. intro n. 
          destruct (n <?A elem) eqn:?; destruct (n =?A elem) eqn:?; auto 3.
        }
        rewrite H0.
        rewrite filter_compose. apply f_equal. 
        assert ((fun n => (negb (n <?A elem) && negb (n =?A elem))%bool) = (fun n => elem <?A n)).
        { apply functional_extensionality. intro n. 
          destruct (n <?A elem) eqn:?; destruct (n =?A elem) eqn:?; simpl; symmetry; lta_solve; auto 3.
        }
        rewrite H8. reflexivity.
      * intro n. specialize (H1 n).
        dest_match.
        -- rewrite count_occ_filter_neg; auto 2. 
           rewrite count_lt; auto 2.
        -- rewrite count_occ_filter_neg; auto 2. 
           rewrite count_lt; auto 2. eapply AT_lt_trans in H3; eauto. 
        -- rewrite count_occ_filter_pos; auto 2.
      * intro n. specialize (H1 n).
        dest_match.
        -- rewrite count_occ_filter_neg; auto 2.
           rewrite count_gt; auto 2.
        -- rewrite count_occ_filter_pos; auto 2. 
        -- rewrite count_occ_filter_neg; auto 2.
           rewrite count_gt; auto 2. apply AT_gt_trans with (x := n) in H; auto 1. 
           destruct o; auto 3.
  Qed.

  Lemma inv_step : forall x Δx st vcx vst,
    inv x st -> inv (x ⊕ Δx ~ vcx) (Δst Δx st vst).
  Proof.
    intros. destruct H as [? [? ?]]. dest_patch vcx list_vc_case; repeat split; simpl; auto 3.
    - exact eqa_dec.
    - apply BST_insert; assumption.
    - apply AggT_insert; assumption. 
    - intro n. destruct (eq_dec n a); subst.
      * rewrite count_insert. rewrite count_occ_insert. auto.
      * rewrite count_insert_rest; auto 3. rewrite count_occ_insert_rest; auto.
    - apply BST_delete; assumption.
    - apply AggT_delete; assumption.
    - intro n.
      destruct (n =?A (nth_safe A x i H2)) eqn:?; lta_solve.
      * rewrite count_delete; auto 3. rewrite count_occ_delete; auto.
      * rewrite count_delete_rest; auto 3. rewrite count_occ_delete_rest; auto.
  Qed.

  Lemma inc_valid : forall x Δx st vsx, 
    Δx ↪ x -> inv x st -> Δf Δx st vsx ↪ f x.
  Proof.
    intros. eapply inv_step in H as H'. Unshelve. all:eauto 1.
    apply count_result_inv in H as Hcount.
    unfold Δf. rewrite Hcount. 
    apply valid_diff.
  Qed.

  Lemma inc_correct : forall x Δx st vcx vsx vcy, 
    inv x st -> f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st vsx ~ vcy.
  Proof.
    intros. eapply inv_step in H as H'. Unshelve. all: eauto 1.
    apply count_result_inv in H as Hcount.
    apply count_result_inv in H' as Hcount'.
    rewrite Hcount'. simpl. 
    unfold Δf.
    Close Scope change_scope.
    pose proof (patch_diff DiffA (result st) (result (Δst Δx st vsx)) (valid_diff _ _ _)).
    erewrite patch_pir_dep; eauto.
  Qed.

End MaxAggTree.
 *)
