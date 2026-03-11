(* Incremental computation for relational algebra operation. *)

From AUTOINC Require Import SetoidOperator Operator Partial Change PairChange SeqChange ListBag BagChange EqDec Tactic ListMap AggregateTree Fold.
From Stdlib Require Import Lia Eqdep_dec Extraction
  Classes.SetoidClass Compare_dec List PeanoNat FunctionalExtensionality.
Local Open Scope bag_scope.
Import ListNotations.

Hint Extern 4 => constructor : core.
Hint Extern 4 => congruence : core.
Hint Extern 4 => lia : core.  

(*
Incremental relational operators:

- union (✓)
- product (✓)
- select (✓)
- difference (x)
- equi-join (✓)
- aggregation (x)

Natural numbers are not adequate for incremental computation, which also denotes that data type has property a ⊖ z ⊕ z = a has potential for incrementalization.

*)

Ltac set_tac :=
  match goal with
  | [_ : ?t1 ⊆ ?t2 |- ?t1 ⊆ (?t2 ⊎ ?t3)] => 
    apply subseteq_trans with (y:=t2); auto 1; apply union_all_ss_left
  | [_ : ?t1 ⊆ ?t2 |- ?t1 ⊆ (?t3 ⊎ ?t2)] =>
    apply subseteq_trans with (y:=t2); auto 1; apply union_all_ss_right
  | [H : ?t1 ⊆ ?t2 |- ?t1 ⊆ (?t3 ⊎ ?t4)] =>
    unfold subseteq in *; unfold union_all in *; 
    let x := fresh "x" in intro x; specialize (H x); 
     repeat rewrite support_app; lia
  end.


Lemma map_pair_not_in_l : forall T1 T2 (l : list T2) (a : T1) (b : T2) c, c <> a -> ~ In (a, b) (map (fun x => (c, x)) l).
Proof.
  x_ind l.  unfold "~"; intros.
  destruct H0.  x_inj. auto. eapply IHl with (b:=b) in H. auto.
Qed.

Lemma map_pair_not_in_r : forall T1 T2 (l : list T2) (a : T1) (b : T2) c, ~ In b l -> ~ In (a, b) (map (fun x => (c, x)) l).
Proof.
  x_ind l. unfold "~". intros.
  destruct H0. x_inj. firstorder.
  eapply IHl; eauto.
Qed. 


Module IncUnionAll : SetoidStatelessDiffOp.
  Parameter T : Type.
  Parameter EqT : EqDec T.
  Existing Instance EqT.

  Definition A := (bag T * bag T)%type.
  Definition B := bag T.
  Definition SoB := bag_Setoid.


  Definition CA := pairc (@bagc T EqT) (@bagc T EqT).
  Definition CB := seqc (@bagc T EqT).

  Definition Δpair := CA.(ΔT).
  Definition Δseq  := CB.(ΔT).

  Definition f b : bag T := let '(b1, b2) := b in union_all b1 b2.

  Definition Δf (c : Δpair) : Δseq := 
    match c with
    | pair_fst c => [c]
    | pair_snd c => [c]
    | pair_both c1 c2 => [c1; c2]
    end.

  Hint Extern 4 => unfold union_all : core.
  Hint Extern 4 => unfold f in *; unfold Δf in * : core.


  Lemma inc_valid : forall x Δx, Δx ↪ x -> Δf Δx ↪ f x.
  Proof.
    intros [? ?] [? | ? |??] ?; simpl in *; auto.
    all: destruct δ eqn:?; try destruct δ0; subst; simpl; auto; try x_inv H; try set_tac.
    all: econstructor; eauto.
    Unshelve.
    all: try econstructor; eauto.
    Unshelve. all: try econstructor; simpl.
    all: try set_tac.
    eapply subseteq_trans with (y:=b0); auto.
    unfold union_all. unfold subseteq; intros x.
    rewrite diff_support_d; auto.
    rewrite support_app; auto.
  Qed.
      
  Lemma support_diff_subset : forall l1 l2 b, l1 ⊆ l2 -> support l1 b <= support l2 b.
  Proof. x_ind l1. Qed.
  
  Lemma inc_correct : forall x Δx vcx,
    f (x ⊕ Δx ~ vcx) == f x ⊕ Δf Δx ~ (inc_valid x Δx vcx).
  Proof.
    intros [? ?] [?|?|??] ? ?; simpl; destruct δ; try destruct δ0;
    simpl in *; auto 1. 
    all: try rewrite !support_app; eauto 1.
    - rewrite diff_support_d, support_diff, support_app, support_diff; eauto.
    - rewrite !support_diff, support_app.
      eapply support_diff_subset with (b:=b) in vcx. 
      auto.
    - destruct vcx as [? vcx].
      rewrite !support_diff, !support_app. 
      eapply support_diff_subset with (b:=b) in vcx. 
      auto.
    - destruct vcx as [vcx ?].
      rewrite !support_diff, !support_app.
      eapply support_diff_subset with (b:=b) in vcx.
      auto.
    - destruct vcx as [vc1 vc2].
      eapply support_diff_subset with (b:=b) in vc1.
      eapply support_diff_subset with (b:=b) in vc2.
      rewrite !support_diff, !support_app.
      auto.
  Qed. 

  (* Extraction "Ocaml/BagOp/IncUnionAll" f Δf.  *)
End IncUnionAll.

Module IncSelect <: SetoidStatelessDiffOp.
  Parameter T : Type.
  Parameter EqT : EqDec T.
  Existing Instance EqT.
  Parameter cond : T -> bool.  (* TODO: investigate incrementalizing cond. *)

  Definition A := bag T. 
  Definition B := bag T.
  Definition CA := @bagc T EqT.
  Definition CB := @bagc T EqT.

  Definition SoB := bag_Setoid.

  Definition f (x : bag T) : bag T := select cond x.
  Definition Δf (Δx : bag_change T) : bag_change T :=
    match Δx with
    | bag_union b => bag_union (select cond b)
    | bag_diff  b => bag_diff (select cond b)
    end.

  Hint Extern 4 => unfold select; dest_match; simpl : core.
  Hint Extern 4 => unfold f : core.
  Hint Extern 4 => unfold Δf : core.

  Lemma inc_valid : forall x Δx,
     @vc A CA Δx x -> @vc B CB (Δf Δx) (f x).
  Proof.
    simpl. intros. 
    destruct Δx; simpl; dest_match; auto 1.
    unfold f.  
    auto using select_mono.
  Qed.

  Lemma inc_correct : forall x Δx vcx,
    f (@patch A CA Δx x vcx) == @patch B CB (Δf Δx) (f x) (inc_valid x Δx vcx).
  Proof.
    unfold equiv; simpl.
    intros [|x] [?|?] ? ?; simpl; auto 1; dest_match;
    simpl; unfold f; unfold "⊎"; try rewrite !support_cons;
    try rewrite !select_app;
    try rewrite !support_app; dest_match; auto 1;
    rewrite select_diff, !support_diff; auto.
  Qed.

  (* Extraction "Ocaml/BagOp/IncSelect" f Δf.  *)

End IncSelect.


Module IncProject <: SetoidStatelessDiffOp.
  Parameter T : Type.
  Parameter U : Type.
  Parameter EqT : EqDec T.
  Parameter EqU : EqDec U.
  Existing Instance EqT.
  Existing Instance EqU.
  
  Parameter g : T -> U.

  Definition A := bag T. 
  Definition B := bag U.
  Definition CA := @bagc T EqT.
  Definition CB := @bagc U EqU.

  Definition SoB := bag_Setoid.

  Definition f (x : bag T) : bag U := bag_map g x.
  Definition Δf (Δx : bag_change T) : bag_change U :=
    match Δx with
    | bag_union b => bag_union (bag_map g b)
    | bag_diff  b => bag_diff (bag_map g b)
    end.

  Hint Extern 4 => unfold f : core.
  Hint Extern 4 => unfold Δf : core.

  Lemma inc_valid : forall x Δx,
     @vc A CA Δx x -> @vc B CB (Δf Δx) (f x).
  Proof.
    simpl. intros. 
    destruct Δx; simpl; dest_match; auto 1.
    unfold f. unfold subseteq in *. intro e.
    eapply support_map_mono. assumption.
  Qed.

  Lemma inc_correct : forall x Δx vcx,
    f (@patch A CA Δx x vcx) == @patch B CB (Δf Δx) (f x) (inc_valid x Δx vcx).
  Proof.
    unfold f.
    x_ind x; auto; simpl in *; try x_inj; auto.
    - rewrite !nil_diff; auto.
    - rewrite !support_cons, bag_map_app; dest_match; f_equal.
    - rewrite support_diff, support_map_diff; auto.
  Qed.

  (* Extraction "Ocaml/BagOp/IncProject" f Δf.  *)

End IncProject.


Module IncProduct <: SetoidStatefulDiffOp.
  Parameter T1 T2: Type.
  Parameter EqT1 : EqDec T1.
  Existing Instance EqT1.
  Parameter EqT2 : EqDec T2.
  Existing Instance EqT2.

  Definition A := (bag T1 * bag T2)%type.
  Definition B := bag (T1 * T2).
  Definition SoB := @bag_Setoid (T1 * T2) _.
  Definition CA := pairc (@bagc T1 EqT1) (@bagc T2 EqT2).
  Definition CB := seqc (@bagc (T1 * T2) _).

  Notation ΔTA := CA.(ΔT).
  Notation ΔTB := CB.(ΔT).

  Definition f (p : A) : B := let '(a, b) := p in product a b.

  Definition ST := A.
  Definition inv : A -> ST -> Prop := fun x => fun y => x = y.
  Definition vs : CA.(ΔT) -> ST -> Prop := pair_vc.
  Definition init := @id A.
  

  Definition df_x Δx y : bag_change (T1 * T2) :=
    match Δx with
    | bag_union b => bag_union (b ⋅ y)
    | bag_diff b => bag_diff (b ⋅ y)
    end.

  Definition df_y Δy x : bag_change (T1 * T2) :=
    match Δy with
    | bag_union b => bag_union (x ⋅ b)
    | bag_diff b => bag_diff (x ⋅ b)
    end.

  Local Obligation Tactic := intros; try match goal with
  | [H : vs _ _ |- _] => inversion H; auto 1
  end
  .

  Program Definition Δf Δt (st : ST) (_ : vs Δt st) : ΔTB :=
    let '(x, y) := st in
    match Δt with
    | pair_fst c => [df_x c y]
    | pair_snd c => [df_y c x]
    | pair_both c1 c2 =>
      let c1' := df_x c1 y in
      let x' := x ⊕ c1 ~ _ in
      let c2' := df_y c2 x' in
      [c1'; c2']
    end. 

  Program Definition Δst Δt (st : ST) (_ : vs Δt st) : ST :=
    let '(x, y) := st in
    match Δt with
    | pair_fst c => (x ⊕ c ~ _, y)
    | pair_snd c => (x, y ⊕ c ~ _)
    | pair_both c1 c2 => (x ⊕ c1 ~ _, y ⊕ c2 ~ _)
    end.
  
  Lemma state_valid :
    forall x Δx st, Δx ↪ x -> inv x st -> vs Δx st.
  Proof.
    unfold inv; unfold vs. unfold ST.
    intros [? ?] [?|?|??] [? ?] ? ?; x_inj; auto.
    inversion H; constructor; auto.
  Qed. 
    
  Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof.
    unfold inv. unfold vs. unfold ST.
    intros [? ?] [?|?|??] [? ?] ? ?; injection sti as ?; subst; simpl; auto.
  Qed. 
  Lemma inv_init : forall x, inv x (init x).
  Proof. easy. Qed. 

  Hint Resolve product_mono_left product_mono_right : core.
  Lemma inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.  
  Proof.
    unfold inv. unfold vs. unfold ST.
    intros [? ?] [?|?|??] [? ?] ? ?; injection sti as ?; subst; simpl; auto.
    - destruct δ; simpl; econstructor; eauto.
      Unshelve. auto. auto. simpl in *. auto. 
    - destruct δ; simpl; econstructor; eauto.
      Unshelve. auto. auto. simpl in *. auto. 
    - destruct δ; destruct δ0; repeat (econstructor; simpl; eauto).
      Unshelve. all: simpl in *; auto 1; try destruct vcx; eauto.
      + unfold subseteq. intros [? ?].
        unfold union_all.
        repeat (repeat rewrite !support_app, !support_prod); auto.
        repeat (rewrite support_app, !support_prod); auto.
        rewrite support_app. 
        rewrite PeanoNat.Nat.mul_add_distr_r. 
        assert (support b0 t0 <= support b2 t0). 
          unfold subseteq in H0. specialize (H0 t0); auto.
        nia.
      + unfold subseteq. intros [? ?].
        unfold union_all.
        rewrite support_diff.
        rewrite support_prod.
        rewrite support_diff.
        rewrite PeanoNat.Nat.mul_sub_distr_r.
        rewrite !support_prod.
        assert (support b0 t0 <= support b2 t0). 
          unfold subseteq in *. specialize (H0 t0); auto.
        assert (support b1 t >= support b t). 
          unfold subseteq in *. specialize (H t); auto.
        nia.
  Qed.

  Hint Extern 4 => unfold subseteq : core.
  Hint Extern 4 => unfold union_all : core.
  Hint Extern 4 => rewrite !support_app : core.
  Hint Extern 4 => rewrite !support_prod : core.
  Hint Extern 4 => rewrite !support_diff : core.
  Hint Extern 4 => nia : core.
  Hint Resolve product_mono_left product_mono_right : core.




  Lemma inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) == f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).  
  Proof.
    unfold inv. unfold vs. unfold ST.
    intros [? ?] [?|?|??] [? ?] ? ?; inversion sti; subst; simpl; intros [t1 t2]; destruct δ; try destruct δ0; simpl; auto 1.
    unfold "⊎".
    all: repeat rewrite ?support_prod, ?support_app, ?support_prod, ?support_diff; try nia.
  Qed. 

    (* Extraction "Ocaml/BagOp/IncProduct" f init Δf Δst.  *)

End IncProduct.

Module JoinOp <: SetoidStatefulDiffOp.
  Import EquiJoin.
  
  (* Merge an index with a bag. *)
  Definition ix_union := build_ix_helper.
  
  (* 
    - L : left bag's element type
    - R : right bag's element type
  *)
  Parameter (L : Type) (R : Type).
  Parameter (K : Type) (lk : L -> K) (rk : R -> K).
  Parameter EqL : EqDec L.
  Parameter EqR : EqDec R.
  Parameter EqK : EqDec K.
  Existing Instance EqL.
  Existing Instance EqR.
  Existing Instance EqK.

  Definition A := (bag L * bag R)%type.
  Definition B := bag (L * R).
  Definition CA := pairc (@bagc L EqL) (@bagc R EqR).
  Definition CB := seqc (@bagc (L * R)%type _).
  
  Definition SoB := @bag_Setoid (L * R) _.  
  
  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).
  
  Definition f x := equi_join lk rk (fst x) (snd x).

  Definition ix K V := dict K (bag V).
  
  Definition ST := (ix K L * ix K R)%type.

  Definition init x := (build_ix lk (fst x), build_ix rk (snd x)).
  
  Definition vs (Δx : ΔA) (st : ST) := vc Δx (ix_to_bag (fst st), ix_to_bag (snd st)).

  Definition ix_union_bag := build_ix_helper.

  Arguments ix_union_bag {_ _ _}.
  
  Definition ix_diff_bag := ix_diff_bag.
  
  Arguments ix_diff_bag {_ _ _ _}.
  
  Definition Δix {C} `{EqDec C} (k : C -> K) (Δx : bag_change C) (st : ix K C) : ix K C :=
  match Δx with
  | bag_union b => ix_union_bag k b st 
  | bag_diff b => ix_diff_bag k st b
  end.

  Definition Δst Δx st (_ : vs Δx st) : ST :=
  match Δx with
  | pair_fst Δbl => (Δix lk Δbl (fst st), snd st)
  | pair_snd Δbr => (fst st, Δix rk Δbr (snd st))
  | pair_both Δbl Δbr => (Δix lk Δbl (fst st), Δix rk Δbr (snd st))
  end.

  Definition ix_lookup := ix_get.
  Arguments ix_lookup {_ _ _}.

  Definition join_ix {C1 C2 C3} (k : C2 -> K) (st : ix K C1) (b : bag C2)
    (f : bag C1 -> bag C2 -> bag C3) : bag C3 :=
    flat_map (fun (x : C2) => f (ix_lookup st (k x)) (cons x nil)) b.


  Definition inv_ix {C} `{EqDec C} (k : C -> K) (b : bag C) (st : ix K C) :=
    join_ix_inv k st /\ forall x, support b x = ix_support st (k x) x.

  Definition inv x st : Prop :=
    inv_ix lk (fst x) (fst st) /\ inv_ix rk (snd x) (snd st).

  Definition Δf_l (Δb : bag_change L) (st : ix K R) : bag_change (L * R) :=
    match Δb with
    | bag_union b => bag_union (join_ix lk st b (fun b a => product a b))
    | bag_diff b => bag_diff (join_ix lk st b (fun b a => product a b))
    end.

  Definition Δf_r (Δb : bag_change R) (st : ix K L) : bag_change (L * R) :=
    match Δb with
    | bag_union b => bag_union (join_ix rk st b (fun a b => product a b))
    | bag_diff b => bag_diff (join_ix rk st b (fun a b => product a b))
    end.


  Definition Δf Δx st (_ : vs Δx st) :=
    match Δx with
    | pair_fst Δbl => [Δf_l Δbl (snd st)]
    | pair_snd Δbr => [Δf_r Δbr (fst st)]
    | pair_both Δbl Δbr => [Δf_l Δbl (snd st); Δf_r Δbr (Δix lk Δbl (fst st))]
    end.

    Ltac bag_rew := repeat match goal with
    | [|- context[support (_ ++ _) _]] => rewrite support_union_d
    | [|- context[support (_ ⊎ _) _]] => rewrite support_union_d
    | [|- context[support (_ ⋅ _) _]] => rewrite support_prod
    | [|- context[support (_ :: _) _]] => rewrite support_cons
    | [|- context[support [] _]] => rewrite support_nil
    | [|- context[support (diff_bag _ _) _]] => rewrite support_diff
    | [|- context[ix_support (build_ix _ _) _ _]] => rewrite ix_support_build_ix
    | [|- context[ix_support (build_ix_helper _ _ _) _ _]] => 
      rewrite ix_support_build_ix_helper
    | [_ : _ ?x = _ ?y |- context[support (match_ix _ _ _) _]] =>
      erewrite match_build_ix_support
    | [_ : _ ?x <> _ ?y |- context[support (match_ix _ _ _) (?x, ?y)]] =>
      erewrite match_build_ix_support_0
    | [|- context[ix_support (EquiJoin.ix_diff_bag _ _ _) _ _]] =>
      erewrite ix_support_diff_ix
    end.

  Lemma join_ix_support_eq_l : 
    forall (x : bag L) (ix_y : ix K R) (l : L) (r : R),
      lk l = rk r ->
      support (join_ix lk ix_y x (fun b a => a ⋅ b)) (l, r) = 
          (ix_support ix_y (lk l) r) * (support x l).
  Proof.
    x_ind x. bag_rew.
    rewrite IHx; dest_match; auto.
    - erewrite support_map; eauto. unfold ix_lookup.
      rewrite H.
      erewrite ix_get_eq. nia.
    - unfold support. rewrite support_not_in. nia.
      eapply map_pair_not_in_l; auto.
  Qed.

  Lemma join_ix_support_neq_l : 
    forall (x : bag L) (ix_y : ix K R) (l : L) (r : R),
      lk l <> rk r -> join_ix_inv rk ix_y ->
      support (join_ix lk ix_y x (fun b a => a ⋅ b)) (l, r) = 0.
  Proof.
    x_ind x. bag_rew. 
    rewrite IHx; auto.
    destruct (eq_dec l a); subst.
    - erewrite support_map; eauto.
      unfold ix_lookup. erewrite ix_get_neq; eauto.
    - unfold support. simpl.
      erewrite support_not_in. lia.
      apply map_pair_not_in_l. auto.
  Qed.

  Lemma join_ix_support_eq_r : 
    forall (y : bag R) (ix_x : ix K L) (l : L) (r : R),
      lk l = rk r ->
      support (join_ix rk ix_x y (fun a b => a ⋅ b)) (l, r) = 
          (ix_support ix_x (lk l) l) * (support y r).
  Proof.
    x_ind y. bag_rew. rewrite IHy; auto. dest_match.
    - unfold ix_lookup. rewrite <- H.  
      erewrite ix_get_eq. nia.
    - nia.
  Qed. 

  Lemma join_ix_support_neq_r : 
    forall (y : bag R) (ix_x : ix K L) (l : L) (r : R),
      lk l <> rk r -> join_ix_inv lk ix_x ->
      support (join_ix rk ix_x y (fun a b => a ⋅ b)) (l, r) = 0.
  Proof.
    x_ind y. bag_rew. 
    rewrite IHy; auto.
    destruct (eq_dec r a); subst.
    - unfold ix_lookup. erewrite ix_get_neq; eauto.
    - dest_match; auto.
  Qed.

  Ltac join_rew := repeat match goal with
  | [_ : _ ?x = _ ?y |- 
      context[support (join_ix _ _ _ (fun a b => b ⋅ a)) (?x, ?y)]] =>
    erewrite join_ix_support_eq_l
  | [_ : _ ?x = _ ?y |- 
      context[support (join_ix _ _ _ (fun a b => a ⋅ b)) (?x, ?y)]] =>
    erewrite join_ix_support_eq_r
  | [_ : _ ?x <> _ ?y |- 
      context[support (join_ix _ _ _ (fun a b => b ⋅ a)) (?x, ?y)]] =>
    erewrite join_ix_support_neq_l
  | [_ : _ ?x <> _ ?y |- 
      context[support (join_ix _ _ _ (fun a b => a ⋅ b)) (?x, ?y)]] =>
    erewrite join_ix_support_neq_r
  end.
  
  Lemma state_valid : forall (x : A) (Δx : ΔA) (st : ST),
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof.
    unfold inv, vs. simpl.
    intros [x y] [?|?|??] [? ?] ? [? ?]; 
    destruct δ; try destruct δ0; simpl in *; auto;
    unfold inv_ix in *; try econstructor;
    destruct H0 as [Hl1 Hl2]; destruct H1 as [Hr1 Hr2]; auto;
    unfold "⊆" in *; intros; erewrite ix_support_in; eauto;
    erewrite <- ?Hl2, <- ?Hr2; eauto; destruct H; eauto.
  Qed.
     

  Hint Resolve EqL EqR diff_ix_prop : core.
  Hint Extern 4 => apply build_ix_prop : core.

  Lemma inv_init : forall x, inv x (init x). 
  Proof.
    unfold inv. intros [? ?]; simpl; unfold inv_ix;
    repeat split;
    eauto; intros.
    - rewrite ix_support_build_ix; auto.
    - rewrite ix_support_build_ix; auto.
  Qed.

  Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
     inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof.
    unfold inv, inv_ix. 
    intros [? ?] [?|?|??] [??] vcx [[? ?] [? ?]];
    destruct δ; try destruct δ0; simpl in *; repeat split; intros; eauto.
    all: rewrite ?support_app, ?support_diff, ?ix_support_build_ix_helper, ?ix_support_diff_ix, ?e, ?e0; eauto.
  Qed.


  Ltac my_rew := repeat (bag_rew; join_rew).

  Lemma inc_valid : forall (x : A) (Δx : ΔA) (st : ST) (vcx : @vc A CA Δx x) (sti : inv x st) ,
    @vc B CB (Δf Δx st (state_valid x Δx st vcx sti)) (f x).
  Proof with nia.
    unfold inv, inv_ix, f, equi_join. 
    intros [x y] [?|?|??] [lx rx] ? [[? ?] [??]]; 
    destruct δ; try destruct δ0; simpl in *; repeat econstructor.
    Unshelve. all: simpl; try econstructor; unfold "⊆" in *; intros [? ?].
    all: destruct (eq_dec (lk l) (rk r)).
    all: unfold ix_union_bag, ix_diff_bag; my_rew; eauto.
    - rewrite e1, <- e0.
      specialize (vcx l)... 
    - rewrite <- e. specialize (vcx r)... 
    - rewrite <- e, e1, <-e0. destruct vcx as [? vcx]. 
      specialize (vcx r)...
    - rewrite e1, <- e0. destruct vcx as [vcx _]. specialize (vcx l)...
    - rewrite e1, <- e0. destruct vcx as [vcx _]. specialize (vcx l)...
    - rewrite <- e, e1, <- e0. destruct vcx as [vcx vcy]. 
      specialize (vcx l). specialize (vcy r)...
  Qed.

  Lemma inc_correct : forall (x : A) (Δx : ΔA) (st : ST) (vcx : @vc A CA Δx x) 
    (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) == @patch B CB (Δf Δx st (state_valid x Δx st vcx sti)) (f x) (inc_valid x Δx st vcx sti).
  Proof with nia.
    unfold inv, f, equi_join, inv_ix. 
    intros [x y] [?|?|??] [lx rx] ? [[??] [??]] [? ?];
    destruct (eq_dec (lk l) (rk r));
    destruct δ; try destruct δ0; simpl in *; unfold "⊎", ix_union_bag, ix_diff_bag; subst; my_rew; eauto.
    - rewrite e1, <- e0... 
    - rewrite e1, <- e0...
    - rewrite <- e... 
    - rewrite <- e...
    - rewrite <- e, e1, <- e0... 
    - rewrite <- e, e1, <- e0...
    - rewrite <- e, e1, <- e0...
    - rewrite <- e, e1, <- e0...
  Qed.

  (* Extraction "Ocaml/BagOp/IncJoin" f init Δf Δst.  *)
End JoinOp.



(** Incremental Datalog aggregation. *)
Module DatalogAggregation (PreOrd : STRICT_PRE_ORDER) (Join : JOIN PreOrd) <: StatefulDiffOp.

  Module Import Agg := AggregateTree PreOrd Join.
  Import PreOrd Join.
  Module Import F := STRICT_PRE_ORDER_FACTS(PreOrd).
  Import Difference.
  

  Instance eqE : EqDec E := eqa_dec.
  Parameter DiffE : difference E.
  Definition CE := cdiff E DiffE.

  Definition A := bag E.
  Definition B := E.
  Definition CA := @bagc E eqE.
  Definition CB := CE.


  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).

  Implicit Type t : A.
  Implicit Type Δt : ΔA.
  Definition ST : Type := AT.

  Definition init (t : A) := 
    fold_left insert t Empty.

  Definition vs (dt1 : ΔA) (st : ST) : Prop := True.


  Definition Δst Δt st (_ : vs Δt st) : ST := 
    match Δt with
    | bag_union b => fold_left insert b st
    | bag_diff b => fold_left delete b st
    end.


  Definition inv (l : bag E) (st : AT) : Prop :=
    BST st /\ AggT st 
    /\ forall n, count_occ eq_dec l n = count n st
    .
  Definition f := fold_right join bottom. 

  Definition Δf Δt st (H : vs Δt st) : ΔB :=
    let st' := Δst Δt st H in
    (result st') ⊖ (result st).

  Hint Extern 4 => unfold vs : core.
  Hint Extern 4 => unfold inv : core.
  Hint Extern 4 => unfold Δf : core.
  Hint Extern 4 => unfold Δst : core.
  Lemma state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof. auto. Qed.
  Lemma init_count : forall x (t : AT) n,
    BST t ->
    count n (fold_left insert x t) = 
    count n (fold_left insert x Empty) +
    count n t.
  Proof.
    induction x; intros; simpl; auto 1.
    rewrite IHx. symmetry. rewrite IHx. simpl.
    dest_match.
    - rewrite count_insert. lia.
    - rewrite count_insert_rest; auto 1.
    - destruct s; subst. congruence.  
      rewrite count_insert_rest; auto.
    - constructor; auto 1. repeat split; try constructor; try lia.
    - apply BST_insert; auto.
  Qed. 

  Lemma inv_init : 
    forall x , inv x (init x).
  Proof. 
    unfold init. 
    intros x; repeat split. 
    - apply fold_left_ind, BST_insert; auto.
    - apply fold_left_ind; intros; subst; try constructor. apply AggT_insert; auto.
    - induction x; intros; simpl; try lia. rewrite IHx. dest_match.
      + rewrite init_count; auto 1.
        symmetry.
        rewrite init_count; simpl. dest_match; try lia; try congruence.
        repeat split; lia.
      + rewrite init_count; auto 1.
        symmetry.
        rewrite init_count; simpl. dest_match; try lia; try congruence.
        repeat split; lia. 
  Qed.

  Hint Resolve BST_insert BST_delete AggT_insert AggT_delete : core.
  Lemma inv_step_count_insert : forall b st n,
    BST st ->
    count n (fold_left insert b st) = count n st + count_occ eq_dec b n.
  Proof.
    induction b; simpl; intros. auto. 
    dest_match.
    - rewrite IHb, count_insert. auto. apply BST_insert. auto.
    - rewrite IHb, count_insert_rest; auto. 
  Qed. 

  Lemma inv_step_count_delete : forall b st n,
    BST st ->
    count n (fold_left delete b st) = count n st - count_occ eq_dec b n.
  Proof.
    induction b; simpl; intros; try lia.
    dest_match.
    - rewrite IHb, count_delete; auto 1. auto. 
    - rewrite IHb, count_delete_rest; auto 1. auto.
  Qed. 

  Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof. 
    unfold inv, Δst. intros ? [?|?] ? ? [? [? ?]]. 
    repeat split.
    - apply fold_left_ind; intros; subst; simpl; auto. 
    - apply fold_left_ind; intros; subst; simpl; auto.
    - intros. rewrite inv_step_count_insert; simpl. 
      unfold "⊎"; rewrite count_occ_app; auto. auto.
    - repeat split. 
      + apply fold_left_ind; auto.
      + apply fold_left_ind; auto.
      + simpl. intros. rewrite inv_step_count_delete, <- !count_occ_support.
        rewrite support_diff. rewrite !count_occ_support. auto. auto. 
  Qed.  
  Lemma f_filter : forall (l : list E) (g : E -> bool),
  f l = join (f (filter (fun n => g n) l)) (f (filter (fun n => negb (g n)) l)).
  Proof.
    induction l; intros. join_reduce.
    simpl. dest_match; auto 3; simpl.
    - rewrite <- join_assoc. rewrite <- IHl. reflexivity.
    - rewrite join_assoc. join_comm (f (filter (fun n : E => g n) l)) a.
      rewrite <- join_assoc. rewrite <- IHl. reflexivity.
  Qed.

  Lemma filter_nocount : forall l elem,
    count_occ eq_dec l elem = 0 -> filter (fun n => n =?E elem) l = [].
  Proof.
    induction l; intros. auto.
    simpl. dest_match; simpl in *; dest_match; auto 3.
  Qed.

  Lemma f_filter_eq : forall l elem,
    f (filter (fun n => n =?E elem) l) = elem_join elem (count_occ eq_dec l elem).
  Proof.
    induction l; intros; simpl; auto 3. 
    dest_match; simpl; auto 3.
    rewrite IHl. dest_match; auto 2.
  Qed.

  Lemma filter_compose : forall T (l : list T) f g,
    filter f (filter g l) = filter (fun n => andb (f n) (g n)) l.
  Proof. 
    induction l; intros. auto.
    simpl. dest_match; auto 3; simpl; dest_match; auto 3.
    rewrite IHl. reflexivity.
  Qed.

  Lemma count_occ_filter_neg : forall l f (n : E),
    f n = false -> count_occ eq_dec (filter f l) n = 0.
  Proof.
    induction l; intros. auto.
    simpl. dest_match; auto 2.
    rewrite count_occ_cons_neq; auto 2.
  Qed.

  Lemma count_occ_filter_pos : forall l f n,
    f n = true -> count_occ eq_dec (filter f l) n = count_occ eq_dec l n.
  Proof.
    induction l; intros. auto.
    simpl. dest_match; auto 2.
    - rewrite count_occ_cons_eq; auto.
    - rewrite count_occ_cons_neq; auto.
  Qed.


  Lemma count_result_inv : forall st l,
    inv l st -> f l = result st.
  Proof.
    induction st; intros l [H [H0 H1]].
    - simpl in *. apply count_occ_inv_nil in H1. subst. reflexivity.
    - destruct H as [? [? [? [? ?]]]]. destruct H0 as [? [? ?]]. subst.
      simpl in *. 
      rewrite <- IHst1 with (l := filter (fun n => n <?E elem) l); repeat split; auto 3.
      rewrite <- IHst2 with (l := filter (fun n => elem <?E n) l); repeat split; auto 3.
      * rewrite f_filter with (g := fun n => n =?E elem).
        rewrite f_filter_eq.
        rewrite f_filter with (g := fun n => n <?E elem).
        rewrite filter_compose. rewrite join_comm. f_equal.
        assert ((fun n => ((n <?E elem) && negb (n =?E elem))%bool) = (fun n => n <?E elem)).
        { apply functional_extensionality. intro n. 
          destruct (n <?E elem) eqn:?; destruct (n =?E elem) eqn:?; auto 3.
        }
        rewrite H0.
        rewrite filter_compose. apply f_equal. 
        assert ((fun n => (negb (n <?E elem) && negb (n =?E elem))%bool) = (fun n => elem <?E n)).
        { apply functional_extensionality. intro n. 
          destruct (n <?E elem) eqn:?; destruct (n =?E elem) eqn:?; simpl; symmetry; lta_solve; auto 3.
        }
        rewrite H8. reflexivity.
        specialize (H1 elem). dest_match; auto 3.
      * intro n. specialize (H1 n).
        dest_match.
        -- rewrite count_occ_filter_neg; auto 2. 
          rewrite count_lt; auto 2.
        -- rewrite count_occ_filter_neg; auto 2. 
          rewrite count_lt; auto 2. eapply AT_lt_trans in H3; eauto. 
        -- rewrite count_occ_filter_pos; auto 2.
          destruct s; auto.
      * intro n. specialize (H1 n).
        dest_match.
        -- rewrite count_occ_filter_neg; auto 2.
          rewrite count_gt; auto 2.
        -- rewrite count_occ_filter_pos; auto 2. 
        -- rewrite count_occ_filter_neg; auto 2; [.. | destruct s; auto].
          rewrite count_gt; auto 2. apply AT_gt_trans with (x := n) in H; auto 1;
          destruct s; auto 3.
  Qed.


  Lemma inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.
  Proof.
    intros. 
    (* specialize (inv_step x Δx st vcx sti) as ?. *)
    apply count_result_inv in sti as Hcount.
    unfold Δf. rewrite Hcount. 
    apply valid_diff.
  Qed.
    
  Lemma inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).
  Proof.
    unfold Δf.
    intros.
    apply count_result_inv in sti as Hcount.
    assert (forall v1 v2, f (x ⊕ Δx ~ v1) = result (Δst Δx st v2)).
    intros. erewrite count_result_inv. eauto. eapply inv_step.
    erewrite patch_pir_dep with (t2:=result st).
    2: eauto.
    2: eauto.
    erewrite H.
    erewrite patch_pir_dep; eauto 2.
    rewrite (patch_diff DiffE). auto.
    Unshelve. auto. apply valid_diff. apply valid_diff.
  Qed.

  (* Extraction "Ocaml/BagOp/IncAggregate" f init Δf Δst.  *)
End DatalogAggregation.

