(* Signatures for various kinds of incremental operators. *)

From AUTOINC Require Import Change PairChange SeqChange Tactic.
From Stdlib Require Import List.

Module Type StatelessDiffOp.
  (**
  Stateless incremental operator:
  Given a normal operator 
        f : A -> B, 
  a stateless operator Δf : ΔA -> ΔB ought to 
  produce a correct output change to the output solely 
  based on the input change, s.t.
  f (t ⊕ ΔA) = (f t) ⊕ (Δf ΔA)
  *)

  Parameter A B : Type.
  Parameter CA : change A.
  Parameter CB : change B.

  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).
  
  Parameter f : A -> B. (* original function *)
  
  Parameter Δf : ΔT CA -> ΔT CB. (* incremental function *)
  
  Axiom inc_valid : forall x Δx, vc Δx x -> vc (Δf Δx) (f x).

  Axiom inc_correct : forall x Δx vcx vcy,
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx ~ vcy.

End StatelessDiffOp.

Module SeqStatelessDiffOp (op : StatelessDiffOp) <: StatelessDiffOp.
  Definition A := op.A.
  Definition B := op.B.
  Definition CA := seqc op.CA.
  Definition CB := seqc op.CB.
  Definition f := op.f.
  Fixpoint Δf (xs : (ΔT CA)) : (ΔT CB) :=
    match xs with
    | nil => nil
    | Δhd :: Δtl => op.Δf Δhd :: Δf Δtl
    end. 
    
  Lemma inc_valid : forall x Δx, vc Δx x -> vc (Δf Δx) (f x).
  Proof. 
    intros x Δx. revert x. induction Δx as [|Δhd Δtl IH]; intros; simpl.
    - constructor.
    - x_inv H. econstructor. erewrite <- op.inc_correct. apply IH. apply H4.
    Unshelve. apply op.inc_valid. auto.
  Qed.

  Lemma inc_cons : forall Δhd Δtl, Δf (Δhd :: Δtl) = op.Δf Δhd :: Δf Δtl.
  Proof. auto. Qed.

  Arguments patch : clear implicits.

  Lemma inc_correct : forall (x : A) (Δx : (ΔT CA)) (vcx : vc Δx x) (vcy : vc (Δf Δx) (f x)),
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx ~ vcy.
  Proof.
    unfold f.
    intros x Δx. revert x. induction Δx as [|Δhd Δtl IH]; intros.
    - auto.
    - replace (@patch op.A CA (cons Δhd Δtl) x vcx) with (seq_patch op.CA (Δhd :: Δtl) x vcx); auto.
      replace (@patch op.B CB (Δf (cons Δhd Δtl)) (op.f x) vcy) with (seq_patch op.CB (Δf (cons Δhd Δtl)) (op.f x) vcy); auto.
      (* symmetry. erewrite seq_patch_pir. symmetry. erewrite seq_patch_pir. *)
      inversion vcx. inversion vcy. subst. erewrite seq_patch_cons.
      assert (H9 := H8). erewrite <- op.inc_correct in H9.
      simpl in IH. erewrite IH.
      simpl.
      erewrite seq_patch_pir_dep.
      erewrite seq_patch_pir_dep. 
      all: eauto.
      erewrite op.inc_correct; eauto.
      Unshelve. all: eauto.
    Qed.
End SeqStatelessDiffOp.



Module Type StatefulDiffOp.
  (**
  Stateful incremental operators:
  Given a normal operator 
        f : A -> B, 
  a stateful operator Δf : ΔA -> ST -> ΔB * ST maintains a state st and 
  keeps the following specification during incrementalization, where 
  `inv` is an invariant that ensures the state is compatible with the latest 
  input to f.

  - output is correct : inv t st -> f (t ⊕ Δt) = f t ⊕ (Δf Δt st)._1
  - state is updated correctly : inv t st -> inv (t ⊕ Δt) (Δf Δt st)._2

  *)

  Parameter (A : Type) (B : Type).
  Parameter (CA : change A) (CB : change B).
  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).
  

  Parameter ST : Type. (* state of incremental function *)
  Parameter init : A -> ST.
  Parameter vs : ΔA -> ST -> Prop.
  Parameter Δst : forall Δx st, vs Δx st -> ST. 

  Parameter inv : A -> ST -> Prop.
  Axiom state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Axiom inv_init : forall x, inv x (init x). 
  Axiom inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).

  Parameter f : A -> B. (* original function *)
  Parameter Δf : forall Δx st, vs Δx st -> ΔB. 

  Axiom inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.
  
  Axiom inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).

End StatefulDiffOp.

Module Type InputDiffOp.

  (*
  Stateful incremental opreator which maintains its latest input as the state.
  *)
  Parameter A B : Type.
  Parameter CA : change A.
  Parameter CB : change B.  
  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).
  
  Parameter f : A -> B. (* original function *)

  Notation vci := (@vc A CA).

  Parameter Δf : forall Δt (t : A), vci Δt t -> ΔB. 

  Axiom inc_valid : forall Δx x vcx, Δf Δx x vcx ↪ f x.
  
  Axiom inc_correct : forall Δx x vcx vcy, 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx x vcx ~ vcy.

End InputDiffOp.

Module InputDiffOpFunctor (op : InputDiffOp) <: StatefulDiffOp.
    
  Definition A := op.A.
  Definition B := op.B.
  Definition CA := op.CA.
  Definition CB := op.CB.

  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).

  Definition f := op.f.

  Definition ST := A.

  Definition inv := @eq A.

  Definition vs := @vc A CA.

  Definition Δf := op.Δf.

  Definition init (t : A) := t.

  Program Definition Δst Δt st (v : vs Δt st) : ST :=
    @patch A CA Δt st _. 
  
  Lemma inv_init : forall x, inv x (init x).
  Proof. unfold init. unfold inv. auto. Qed. 
  
  Lemma init_valid : forall t Δt, vc Δt t -> vs Δt (init t).
  Proof. unfold vs. auto. Qed. 

 
  Lemma state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof. unfold inv. unfold vs. intros; subst; auto. Qed.

  Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
  inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof. 
    unfold inv. intros. subst. unfold Δst. auto. 
  Qed. 

  Lemma inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
  Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.
  Proof. unfold inv. intros. subst. apply op.inc_valid. Qed.
  
  Lemma inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
  f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).
  Proof. unfold inv. intros. subst. erewrite patch_det. apply op.inc_correct. Qed.

End InputDiffOpFunctor.



Module Type SFInOutOP.

  (*
  Stateful incremental opreator which maintains its 
  latest input and output as the state.
  *)
  Parameter A B : Type.
  Parameter CA : change A.
  Parameter CB : change B.  
  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).
  
  Parameter f : A -> B. (* original function *)

  Notation vci := (@vc A CA).

  Implicit Type i : A.
  Implicit Type o : B.

  Parameter Δf : forall Δt i o, vci Δt i -> ΔB. 

  Axiom inc_valid : forall Δx i o vsx, Δf Δx i o vsx ↪ o.
  
  Axiom inc_correct : forall Δx i vcx vsx vcy, 
    f (i ⊕ Δx ~ vcx) = f i ⊕ Δf Δx i (f i) vsx ~ vcy.

End SFInOutOP.

Module SFInOutOPFunctor (op : SFInOutOP) <: StatefulDiffOp.
    
  Definition A := op.A.
  Definition B := op.B.
  Definition CA := op.CA.
  Definition CB := op.CB.

  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).

  Definition f := op.f.

  Definition ST := (A * B)%type.

  Definition inv : A -> ST -> Prop := fun t st => (t, f t) = st.

  Definition vs : ΔA -> ST -> Prop := fun Δt st => vc Δt (fst st).

  Definition Δf Δt st : vs Δt st -> ΔB := 
    let '(i, o) := st in op.Δf Δt i o.

  Definition init (t : A) := (t, f t).

  Lemma inv_init : forall x, inv x (init x).
  Proof. unfold init. unfold inv. auto. Qed. 

  Lemma state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof. unfold inv. unfold vs. intros; subst; auto. Qed.
  
  Lemma inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
  Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.
  Proof. 
    unfold inv. intros. subst. apply op.inc_valid.  
  Qed.

  Program Definition Δst Δt st (v : vs Δt st) : ST :=
    let '(i, o) := st in
    (i ⊕ Δt ~ v, o ⊕ Δf Δt (i, o) v ~ (op.inc_valid Δt i o _)).
    

  Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
  inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof. 
    unfold inv. intros. destruct st.  
    injection sti as ?;  subst. unfold Δst. f_equal; auto.
    apply op.inc_correct.  
  Qed. 


  Lemma inc_correct :forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
  f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).
  Proof. unfold inv. intros. subst. apply op.inc_correct. Qed.

End SFInOutOPFunctor.


(* TODO: define tactics for proving inc_valid and inc_correct *)