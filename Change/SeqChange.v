From AUTOINC Require Import Change EqDec NatChange Tactic.
From Stdlib Require Import List.
Import ListNotations.

Section SeqChange.
  Variable T : Type.

  Variable C : change T.

  (* Use an explicit constructor to help the type checker, as Coq cannot tell a list of change can be the value of seq_change.  *)
  Definition seq_change := list C.(ΔT).

  Inductive seq_vc : seq_change -> T -> Prop :=
  | vc_nil : forall t, seq_vc nil t
  | vc_cons : forall Δhd Δtl t H,
    seq_vc Δtl (t ⊕ Δhd ~ H) ->
    seq_vc (Δhd :: Δtl) t.

  Lemma seq_vc_p_dep : forall c1 c2 t1 t2, 
    c1 = c2 -> t1 = t2 -> seq_vc c1 t1 -> seq_vc c2 t2.
  Proof. intros; subst; auto. Qed.

  Local Obligation Tactic := intros; subst; try match goal with [H:seq_vc (_::_) _ |- _] => x_inv H end; try erewrite patch_det; eauto.
  
  Program Fixpoint seq_patch Δt t (vc : seq_vc Δt t) : T :=
    match Δt with
    | nil => t
    | Δhd::Δtl=> seq_patch Δtl (t ⊕ Δhd) _
    end.  

  Lemma seq_patch_noc : forall t v, seq_patch [] t v = t.
  Proof. auto. Qed.

  Lemma seq_patch_pir_dep : forall Δl1 Δl2 t1 t2 vc1 vc2,
    Δl1 = Δl2 -> t1 = t2 -> seq_patch Δl1 t1 vc1 = seq_patch Δl2 t2 vc2.
  Proof.
    induction Δl1; simpl; intros; subst. simpl. auto.
    simpl.
    erewrite IHΔl1; eauto.  
  Qed. 

  Hint Resolve seq_patch_pir_dep : core.
  Lemma seq_patch_pir : forall Δt t vc1 vc2, 
    seq_patch Δt t vc1 = seq_patch Δt t vc2.
  Proof. auto. Qed.

  Lemma seq_patch_cons : forall Δhd Δtl t v1 v2 v3,
    seq_patch (Δhd :: Δtl) t v1 = seq_patch Δtl (patch Δhd t v2) v3.
  Proof. intros. simpl. auto. Qed. 

  Hint Resolve seq_patch_noc : core.
  Hint Extern 4 => rewrite seq_patch_noc : core.


  Lemma seq_vc_app : forall l1 l2 t v,
    seq_vc l1 t ->
    seq_vc l2 (seq_patch l1 t v) ->
    seq_vc (l1 ++ l2) t.
  Proof.
    induction l1; simpl; intros; auto.
    inversion H; subst.
    eapply vc_cons with (H:=H1).
    eapply IHl1 in H0. 
    erewrite patch_det. eauto.
    erewrite patch_det. eauto.
  Qed.

  Hint Resolve seq_patch_pir : core.
  Hint Resolve seq_patch_noc : core.

  Program Definition seqc : change T := {|
    ΔT  := seq_change
  ; vc := seq_vc
  ; patch := seq_patch
  |}.

End SeqChange.

Arguments seqc {T}.
Global Transparent seq_patch.

Arguments vc_nil {T C}.
Arguments vc_cons [T C].
Arguments seq_vc {T C}.
Arguments seq_change {T}.
Arguments seq_patch {T}.

Hint Extern 4 => rewrite seq_patch_noc : core.
Hint Resolve seq_patch_pir_dep : core.
Lemma seq_patch_if : 
  forall T B (c : change T) (b : {B} + {~B}) l1 l2 t v1 v2 v3, 
    seq_patch c (if b then l1 else l2) t v1 =
    if b then seq_patch c l1 t v2 else seq_patch c l2 t v3.
Proof.
  intros. dest_match; eauto.
Qed.

Lemma seq_patch_app : forall T (c : change T) l1 l2 t v1 v2 v3, 
  seq_patch c (l1 ++ l2) t v1 = 
  seq_patch c l2 (seq_patch c l1 t v2) v3. 
Proof.
  x_ind l1. erewrite IHl1.
  repeat eapply seq_patch_pir_dep; eauto.
  Unshelve.
  + inversion v2; subst. erewrite patch_pir_dep; eauto.
  + inversion v3; subst. constructor. erewrite seq_patch_pir_dep; eauto.
Qed.

Definition vc_free {T} (c : change T) Δt := forall t, c.(vc) Δt t.
Definition list_vc_free {T} {c : change T} (l : list c.(ΔT)) := 
  Forall (vc_free c) l
.

Lemma seq_vc_free {T} : forall (c : change T) (l : seq_change c) (t : T), list_vc_free l -> seq_vc l t. 
Proof.
  unfold list_vc_free, vc_free.
  x_ind l. constructor.
  inversion H; subst.
  econstructor. Unshelve. 2: eauto.
  eapply IHl. eauto.
Qed. 
