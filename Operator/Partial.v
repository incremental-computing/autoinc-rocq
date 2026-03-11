(* From AUTOINC Require Import Change SeqChange PairChange Operator Tactic.
From Stdlib Require Import List.
Import ListNotations.

Local Open Scope type_scope.




Module Type SLPartialOP.
  
  Parameter T1 T2 T3 : Type.
  Parameter C1 : change T1.
  Parameter C2 : change T2.
  Parameter C3 : change T3.


  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).
  Notation ΔT3 := C3.(ΔT).

  
  Parameter f : T1 -> T2 -> T3. (* original function *)
  
  Parameter df_x : ΔT1 -> ΔT3. 
  Parameter df_y : ΔT2 -> ΔT3. 


  Axiom inc_valid_x : forall x y Δx,
     Δx ↪ x -> df_x Δx ↪ f x y.

  Axiom inc_valid_y : forall x y Δy,
     Δy ↪ y -> df_y Δy ↪ f x y.

  Axiom inc_correct_x : forall x y Δx vc1 vc2,
    f (x ⊕ Δx ~ vc1) y = f x y ⊕ df_x Δx ~ vc2.
  
  Axiom inc_correct_y : forall x y Δy vc1 vc2,
    f x (y ⊕ Δy ~ vc1) = f x y ⊕ df_y Δy ~ vc2.

End SLPartialOP.

Module SLPartialOPFacts (Import op : SLPartialOP).
  Lemma inc_correct_both1 : forall x y Δx Δy vc1 vc2 vc3 vc4,
    f (x ⊕ Δx ~ vc1) (y ⊕ Δy ~ vc2) = 
    (f x y ⊕ df_x Δx ~ vc3) ⊕ df_y Δy ~ vc4.
  Proof.
    intros. 
    pose proof vc4 as vc5.
    erewrite <- inc_correct_x in vc5. 
    erewrite inc_correct_y with (vc2:=vc5).
    assert (f (patch Δx x vc1) y = patch (df_x Δx) (f x y) vc3).
    { apply inc_correct_x. }
    eapply patch_pir_dep; auto.
  Qed.

  Lemma inc_correct_both2 : forall x y Δx Δy vc1 vc2 vc3 vc4,
    f (x ⊕ Δx ~ vc1) (y ⊕ Δy ~ vc2) =
    (f x y ⊕ df_y Δy ~ vc3) ⊕ (df_x Δx) ~ vc4.
  Proof.
    intros. 
    pose proof vc4 as vc5.
    erewrite <- inc_correct_y in vc5. 
    erewrite inc_correct_x with (vc2:=vc5).
    assert (f x (patch Δy y vc2) = f x y ⊕ df_y Δy ~ vc3).
    { apply inc_correct_y. }
    eapply patch_pir_dep; auto.
  Qed.
End SLPartialOPFacts.

Module SLPartialOPFunctor (op : SLPartialOP) <: StatelessDiffOp.
  (*
  This module functor can convert a Partial stateless incremental operator 
  to a general stateless incremental operator.

  In other words, an Partial stateless op refines a general stateless op.
  *)

  Module m := SLPartialOPFacts op.
  Import m.
  Definition T1 := (op.T1 * op.T2)%type.
  Definition T2 := op.T3.

  Definition C1 := pairc op.C1 op.C2.
  Definition C2 := seqc op.C3.

  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).

  Definition f (t : T1) : T2 :=
    let '(t1, t2) := t in op.f t1 t2.

  Definition Δf (t : ΔT1) : ΔT2 :=
    match t with
    | pair_noc => []
    | pair_fst c => [op.df_x c]
    | pair_snd c => [op.df_y c]
    | pair_both c1 c2 => [op.df_x c1; op.df_y c2]
    end. 

  Lemma inc_valid : forall x Δx,
    Δx ↪ x -> Δf Δx ↪ f x.
  Proof.
    intros [x1 x2] Δx vcx. 
    inversion vcx; subst; simpl; try econstructor; try constructor.
    econstructor. constructor.
    Unshelve.
    - apply op.inc_valid_x; auto.
    - apply op.inc_valid_y; auto.
    - apply op.inc_valid_x. auto.
    - rewrite <- op.inc_correct_x with (vc1:=X).
      eapply op.inc_valid_y. auto.
  Qed.

  Lemma inc_correct : forall x Δx vcx vcy,
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx ~ vcy.
  Proof.
    simpl.
    intros [x1 x2] Δx vcx vcy. 
    dest_patch vcx pair_vc_case;
    dest_patch_with vcy seq_vc_case pf;
    simpl in *; auto.
    - rewrite seq_patch_noc; apply op.inc_correct_x.
    - rewrite seq_patch_noc; apply op.inc_correct_y.
    - dest_patch_with vc2 seq_vc_case pf0; simpl.
      rewrite seq_patch_noc.
      apply inc_correct_both1.
  Qed.

End SLPartialOPFunctor.

Module Type SLCommOP.
  
  Parameter T1 T2 : Type.
  Parameter C1 : change T1.
  Parameter C2 : change T2.

  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).

  Parameter f : T1 -> T1 -> T2. (* original function *)

  Parameter Δf : ΔT1 -> ΔT2. (* incremental function *)

  Implicit Types x y : T1.
  Implicit Types Δ : ΔT1.  

  Axiom f_comm : forall x y, f x y = f y x.

  Axiom inc_valid : forall x y Δ,
    Δ ↪ x -> Δf Δ ↪ f x y.

  Axiom inc_correct : forall x y Δ vc1 vc2,
    f (x ⊕ Δ ~ vc1) y = f x y ⊕ Δf Δ ~ vc2.

End SLCommOP.

Module SLCommOPFunctor (op : SLCommOP) <: SLPartialOP.

  Definition T1 := op.T1.
  Definition T2 := op.T1.
  Definition T3 := op.T2.

  Definition C1 := op.C1.
  Definition C2 := op.C1.
  Definition C3 := op.C2.

  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).
  Notation ΔT3 := C3.(ΔT).


  Definition f := op.f.
  Definition df_x := op.Δf.
  Definition df_y := op.Δf.


  Hint Resolve op.inc_valid op.inc_correct : core.
  Hint Extern 4 => rewrite op.f_comm : core.

  Lemma inc_valid_x : forall x y Δx,
    Δx ↪ x -> df_x Δx ↪ f x y.
  Proof. auto. Qed.

  Lemma inc_valid_y : forall x y Δy,
    Δy ↪ y -> df_y Δy ↪ f x y.
  Proof. auto. Qed.

  Lemma inc_correct_x : forall x y Δx vc1 vc2,
    f (x ⊕ Δx ~ vc1) y = f x y ⊕ df_x Δx ~ vc2.
  Proof. auto. Qed.

  Lemma inc_correct_y : forall x y Δy vc1 vc2,
    f x (y ⊕ Δy ~ vc1) = f x y ⊕ df_y Δy ~ vc2.
  Proof.
    intros. 
    pose proof vc2 as vc3.
    rewrite op.f_comm in vc3.
    assert (f x y ⊕ df_y Δy ~ vc2 = f y x ⊕ df_y Δy ~ vc3).
      eapply patch_pir_dep; auto.
    rewrite H; auto. 
  Qed.

End SLCommOPFunctor.

Module Type SFPartialOP. (* TODO : rename *)
  Parameter T1 T2 T3 : Type.
  Parameter C1 : change T1.
  Parameter C2 : change T2.
  Parameter C3 : change T3.

  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).
  Notation ΔT3 := C3.(ΔT).

  Parameter f : T1 -> T2 -> T3.
  Parameter df_x : ΔT1 -> T2 -> ΔT3.
  Parameter df_y : ΔT2 -> T1 -> ΔT3.

  Implicit Type x : T1.
  Implicit Type y : T2.
  Implicit Type Δx : ΔT1.
  Implicit Type Δy : ΔT2.

  Axiom inc_valid_x : forall x y Δx, Δx ↪ x -> df_x Δx y ↪ f x y.

  Axiom inc_valid_y : forall x y Δy, Δy ↪ y -> df_y Δy x ↪ f x y.

  Axiom inc_correct_x : forall x y Δx vc1 vc2,
    f (x ⊕ Δx ~ vc1) y  = f x y ⊕ df_x Δx y ~ vc2.

  Axiom inc_correct_y : forall x y Δy vc1 vc2,
    f x (y ⊕ Δy ~ vc1)  = f x y ⊕ df_y Δy x ~ vc2.

End SFPartialOP.



Module SFPartialOPFacts (Import op : SFPartialOP).
  (**
  TODO: note that if we know more about Δf, the following equation can be further unfolded, e.g. 
    mul (x ⊕ Δx) (y ⊕ Δy)
  = mul x y + Δmul Δx y + Δmul Δy (x + Δx)
  = mul x y + Δmul Δx y + Δmul Δy x + ΔΔmul Δy Δx 
  *)
  Lemma inc_correct_both_1 : forall x Δx y Δy vc1 vc2 vc3 vc4,
    f (x ⊕ Δx ~ vc1) (y ⊕ Δy ~ vc2) = 
    (f x y ⊕ df_x Δx y ~ vc3) ⊕ (df_y Δy (x ⊕ Δx ~ vc1)) ~ vc4.
  Proof.
    intros.    
    pose proof vc4 as vc5.
    erewrite <- inc_correct_x in vc5. 
    erewrite inc_correct_y with (vc2:=vc5).
    assert (f (patch Δx x vc1) y = patch (df_x Δx y) (f x y) vc3).
    { apply inc_correct_x. }
    eapply patch_pir_dep; auto.
  Qed.


  Lemma inc_correct_both_2 : forall x Δx y Δy vc1 vc2 vc3 vc4,
    f (x ⊕ Δx ~ vc1) (y ⊕ Δy ~ vc2) = 
    (f x y ⊕ df_y Δy x ~ vc3) ⊕ (df_x Δx (y ⊕ Δy ~ vc2)) ~ vc4.
  Proof.
    intros. 
    pose proof vc4 as vc5.
    erewrite <- inc_correct_y in vc5. 
    erewrite inc_correct_x with (vc2:=vc5).
    assert (f x (patch Δy y vc2) = f x y ⊕ df_y Δy x ~ vc3).
    { apply inc_correct_y. }
    eapply patch_pir_dep; auto.
  Qed.

End SFPartialOPFacts.

Module SFPartialOPFunctor (op : SFPartialOP) <: InputDiffOp.
  Module Import m := SFPartialOPFacts op.

  Definition T1 := op.T1 * op.T2.
  Definition T2 := op.T3.  


  Definition C1 := pairc op.C1 op.C2. 
  Definition C2 := seqc op.C3.

  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).

  Definition f t := let '(x, y) := t in op.f x y.
  Notation vci := (@vc T1 C1).

  Program Definition Δf Δt st (v : vci Δt st) : ΔT2 :=
  match Δt with
  | pair_noc => []
  | pair_fst dx => [op.df_x dx (snd st)]
  | pair_snd dy => [op.df_y dy (fst st)]
  | pair_both dx dy =>
    [op.df_x dx (snd st); op.df_y dy ((fst st) ⊕ dx ~ _)]
  end.
  Next Obligation. inversion v; auto. Defined.
  Hint Extern 4 => constructor : core.
  Hint Extern 4 => unfold f in *; unfold Δf in * : core.

  Hint Resolve op.inc_correct_x op.inc_correct_y op.inc_valid_x op.inc_valid_y : core.


  Lemma inc_valid : forall Δx st vsx, 
    Δf Δx st vsx ↪ f st.
  Proof.
    unfold f. intros ? [stx sty] ?. 
    destruct Δx; simpl; auto; inversion vsx; subst.
    - assert (H : (op.df_x δ sty) ↪ (op.f stx sty)). auto.
      apply vc_cons with (H:=H); auto. 
    - assert (H : (op.df_y δ stx) ↪ (op.f stx sty)). auto.
      apply vc_cons with (H:=H); auto.
    - repeat econstructor.
      Unshelve.
      + auto.
      + rewrite patch_det with (Δt2:=X).
        rewrite <- op.inc_correct_x with (vc1:=X).
        eapply op.inc_valid_y. auto.
  Qed.

  Lemma inc_correct : forall Δx st vcx vsx vcy, 
  f (st ⊕ Δx ~ vcx) = f st ⊕ Δf Δx st vsx ~ vcy.
  Proof.
    simpl. intros Δx [stx sty]. intros.
    dest_patch vcx pair_vc_case.
    dest_patch_with vcy seq_vc_case pf; auto.
    all: simpl.
    - dest_patch_with vcy seq_vc_case pf.
      simpl. rewrite seq_patch_noc. auto.
    - dest_patch_with vcy seq_vc_case pf.
      simpl. rewrite seq_patch_noc. auto.
    - dest_patch_with vcy seq_vc_case pf.
      simpl.
      dest_patch_with vc2 seq_vc_case pf0.
      simpl.
      rewrite seq_patch_noc.
      erewrite <- inc_correct_both_1.
      f_equal; auto.
  Qed.
End SFPartialOPFunctor.

Module Type SFCommOP.
  
  Parameter T1 T2 : Type.
  Parameter C1 : change T1.
  Parameter C2 : change T2.
  
  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).

  Parameter f : T1 -> T1 -> T2.

  Parameter Δf : ΔT1 -> T1 -> ΔT2.
  
  Implicit Types x y : T1.
  Implicit Types Δ : ΔT1.  

  Axiom f_comm : forall x y, f x y = f y x.  

  Axiom inc_valid : forall x y Δ,
    Δ ↪ x -> Δf Δ y ↪ f x y.

  Axiom inc_correct : forall x y Δ vc1 vc2,
    f (x ⊕ Δ ~ vc1) y = f x y ⊕ Δf Δ y ~ vc2.

End SFCommOP.

Module SFCommOPFunctor (op : SFCommOP) <: SFPartialOP.  
  Definition T1 := op.T1.
  Definition T2 := op.T1.
  Definition T3 := op.T2.


  Definition C1 := op.C1.
  Definition C2 := op.C1.
  Definition C3 := op.C2.


  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).

  Definition f := op.f.
  Definition df_x := op.Δf.
  Definition df_y := op.Δf.


  Hint Resolve op.inc_valid op.inc_correct : core.
  Hint Extern 4 => rewrite op.f_comm : core.

  Lemma inc_valid_x : forall x y Δx,
    Δx ↪ x -> df_x Δx y ↪ f x y.
  Proof. intros. auto. Qed.

  Lemma inc_valid_y : forall x y Δy,
    Δy ↪ y -> df_y Δy x ↪ f x y.
  Proof. intros. auto. Qed.

  Lemma inc_correct_x : forall x y Δx vc1 vc2,
    f (x ⊕ Δx ~ vc1) y = f x y ⊕ df_x Δx y ~ vc2.
  Proof. intros. auto. Qed.

  Lemma inc_correct_y : forall x y Δy vc1 vc2,
    f x (y ⊕ Δy ~ vc1) = f x y ⊕ df_y Δy x ~ vc2.
  Proof.     
    intros. 
    pose proof vc2 as vc3.
    rewrite op.f_comm in vc3.
    assert (f x y ⊕ df_y Δy x ~ vc2 = f y x ⊕ df_y Δy x ~ vc3).
      eapply patch_pir_dep; auto.
    rewrite H; auto.
  Qed.

  (* TODO: since the inc_correct_y proof for SLCommOPFunctor and SLCommOPFunctor are almost identical, figure out their relation. *)
 

End SFCommOPFunctor.

Module Type SFPartialInOutOP.
  Parameter T1 : Type.
  Parameter T2 : Type.
  Parameter T3 : Type.

  Parameter C1 : change T1.
  Parameter C2 : change T2.
  Parameter C3 : change T3.

  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).
  Notation ΔT3 := C3.(ΔT).

  Parameter f : T1 -> T2 -> T3.
  Parameter df_x : ΔT1 -> T1 -> T2 -> T3 -> ΔT3.
  Parameter df_y : ΔT2 -> T1 -> T2 -> T3 -> ΔT3.

  Implicit Type x : T1.
  Implicit Type y : T2.
  (* Implicit Type x : T1. *)
  Implicit Type Δx : ΔT1.
  Implicit Type Δy : ΔT2.

  Axiom inc_valid_x : forall x y Δx,
    Δx ↪ x -> df_x Δx x y (f x y) ↪ f x y.
  
  Axiom inc_valid_y : forall x y Δy,
    Δy ↪ y -> df_y Δy x y (f x y) ↪ f x y.

  Axiom inc_correct_x : forall x y Δx vc1 vc2,
    f (x ⊕ Δx ~ vc1) y = f x y ⊕ df_x Δx x y (f x y) ~ vc2.

  Axiom inc_correct_y : forall x y Δy vc1 vc2,
    f x (y ⊕ Δy ~ vc1) = f x y ⊕ df_y Δy x y (f x y) ~ vc2.

End SFPartialInOutOP.



Module SFPartialInOutOPFunctor (op : SFPartialInOutOP) <: StatefulDiffOp.
  Definition T1 := (op.T1 * op.T2)%type.
  Definition T2 := op.T3.

  Definition C1 := pairc op.C1 op.C2.
  Definition C2 := seqc op.C3.
  Notation ΔT1 := C1.(ΔT).
  Notation ΔT2 := C2.(ΔT).
  
  Definition f (t : T1) := let '(x, y) := t in op.f x y.
  Definition ST := op.T1 * op.T2 * op.T3.
  Definition inv (t : T1) (st : ST) := st = (t, f t).  

  Inductive vs_ind : ΔT1 -> ST -> Type :=
    | vs_cond Δt st : 
      vc Δt (fst st) -> snd st = f (fst st) -> vs_ind Δt st.

  Definition vs Δt st := vs_ind Δt st.

  Program Definition Δf (Δt : ΔT1) (st : ST) (_ : vs Δt st) : ΔT2 :=
    let '(x, y, z) := st in
    match Δt with
    | pair_noc => []
    | pair_fst c => [op.df_x c x y z]
    | pair_snd c => [op.df_y c x y z]
    | pair_both cx cy => 
      let cz1 := op.df_x cx x y z in
      let z' := z ⊕ cz1 ~ _ in
      let cz2 := op.df_y cy (x ⊕ cx ~ _) y z' in
      [cz1 ; cz2]
    end.
  Next Obligation. 
    inversion v; subst; auto. simpl in *. subst.  
    apply op.inc_valid_x. inversion X; simpl in *; subst; auto.  
  Defined.
  Next Obligation. 
    inversion v; subst; auto. simpl in *. subst.   
    inversion X; simpl in *; subst; auto.
  Defined.
  

  Program Definition Δst (Δt : ΔT1) (st : ST) (_ : vs Δt st) : ST :=
    let '(x, y, z) := st in
    match Δt with
    | pair_noc => (x, y, z)
    | pair_fst c => (x ⊕ c ~ _, y, op.f (x ⊕ c ~ _) y)
    | pair_snd c => (x, y ⊕ c ~ _, op.f x (y ⊕ c ~ _))
    | pair_both cx cy => 
      (x ⊕ cx ~ _, y ⊕ cy ~ _, op.f (x ⊕ cx ~ _) (y ⊕ cy ~ _))
    end.
  Next Obligation. 
    inversion v; auto. destruct st; simpl in *; x_inj.
    inversion X; auto. 
  Defined.
  Next Obligation. 
  inversion v; auto. destruct st; simpl in *; x_inj.
  inversion X; auto. 
  Defined.
  Next Obligation. 
  inversion v; auto. destruct st; simpl in *; x_inj.
  inversion X; auto. 
  Defined.
  Next Obligation. 
  inversion v; auto. destruct st; simpl in *; x_inj.
  inversion X; auto. 
  Defined.
  Next Obligation. 
  inversion v; auto. destruct st; simpl in *; x_inj.
  inversion X; auto. 
  Defined.
  Next Obligation. 
  inversion v; auto. destruct st; simpl in *; x_inj.
  inversion X; auto. 
  Defined.
  Next Obligation. 
  inversion v; auto. destruct st; simpl in *; x_inj.
  inversion X; auto. 
  Defined.
  Next Obligation. 
  inversion v; auto. destruct st; simpl in *; x_inj.
  inversion X; auto. 
  Defined.

  Definition gen_state (t : T1) : ST := let '(x, y) := t in (x, y, op.f x y). 

  Lemma gen_state_correct : forall x, inv x (gen_state x).
  Proof. unfold gen_state. unfold inv. intros [? ?]. auto. Qed. 
  
  Lemma gen_state_valid : forall t Δt, vc Δt t -> vs Δt (gen_state t).
  Proof. unfold vs. intros [? ?] ? ?. constructor. auto. simpl. auto. Qed. 

  Lemma state_valid : forall x Δx st,
    inv x st -> Δx ↪ x -> vs Δx st.
  Proof.
    unfold inv. intros ? ? [? ?]; intros. constructor; simpl in *;
    x_inj; auto.
  Qed.

  Hint Resolve op.inc_valid_x op.inc_valid_y op.inc_correct_x op.inc_correct_y : core.

  Lemma inv_step : forall x Δx st vcx vst,
     inv x st -> inv (x ⊕ Δx ~ vcx) (Δst Δx st vst).
  Proof.
    simpl.
    unfold inv. intros. destruct st. destruct p.
    destruct x.
    injection H as H; subst.
    dest_patch vcx pair_vc_case; simpl.
    - auto.
    - f_equal. 
      + f_equal; auto. 
      + erewrite op.inc_correct_x. auto. 
    - f_equal. f_equal; auto. 
      erewrite op.inc_correct_y. auto. 
    - f_equal; f_equal; auto.
  Unshelve. all: auto. 
  Qed.

  Hint Extern 4 => constructor : core.
  Lemma inc_valid : forall x Δx st vsx, 
    Δx ↪ x -> inv x st -> Δf Δx st vsx ↪ f x.
  Proof.
    unfold inv.
    intros. destruct x; destruct st. injection H as H; subst.
    inversion X; subst; simpl; auto.
    - econstructor; eauto. Unshelve. auto. 
    - econstructor; eauto. Unshelve. auto.
    - econstructor; econstructor; auto.
      Unshelve. auto. 
      rewrite patch_det with (Δt2:=X0).
      erewrite <- !op.inc_correct_x.
      eauto.
  Qed.

  
  Lemma inc_correct : forall x Δx st vcx vsx vcy, 
    inv x st -> f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st vsx ~ vcy.
  Proof.
    simpl. unfold inv. intros. destruct st. destruct x; destruct p. 
    injection H as H. subst. 
    dest_patch vcx pair_vc_case;
    dest_patch_with vcy seq_vc_case pf;
    simpl; auto; try rewrite seq_patch_noc; auto. 
    erewrite !seq_patch_cons.
    clear pf vc2.
    Unshelve.
    2: {
      rewrite patch_det with (Δt2:=v1).
      erewrite <- !op.inc_correct_x.
      eapply op.inc_valid_y; auto.
    }
    rewrite seq_patch_noc.
    erewrite op.inc_correct_y.
    Unshelve.
    2: {
      auto.
    }
    simpl.
    eapply patch_pir_dep.
    auto. 
    erewrite op.inc_correct_x. 
    symmetry.
    rewrite patch_det with (Δt2:=v1).
    f_equal.
    apply op.inc_valid_y; auto.
  Qed.
    
End SFPartialInOutOPFunctor.
 *)
