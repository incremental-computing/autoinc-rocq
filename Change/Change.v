From Stdlib Require Import Eqdep.
From AUTOINC Require Import EqDec.


Declare Scope change_scope.
Global Open Scope change_scope.

Global Reserved Infix "↪" (at level 60).
Global Reserved Notation "t '⊕' Δt"
  (at level 10, Δt at level 20, left associativity).

(** The signature of data change
- T : the original data type
- ΔT : the raw type of data change
- vc : the type of valid data change
- patch : patching valid changes to data
- patch_det : the patching function should be 
              deterministic to the same pair of (Δt, t)
*)

(** Why not use type classes? Because a data type might have different set of changes.*)
Structure change T : Type := {
    ΔT : Type
  ; vc : ΔT -> T -> Prop where "Δt '↪' t" := (vc Δt t)
  ; patch : forall (Δt : ΔT) t, vc Δt t -> T where "t ⊕ Δt" := (patch _ t Δt)
  ; patch_det : forall t dt (Δt1 Δt2 : dt ↪ t), t ⊕ Δt1 = t ⊕ Δt2
}.
Arguments ΔT {T}.
Arguments vc [T c].
Arguments patch [T c].

Lemma patch_pir_dep : forall A (C : change A) t1 t2 dt1 dt2 H1 H2, 
  t1 = t2 -> dt1 = dt2 ->
  @patch A C dt1 t1 H1 = @patch A C dt2 t2 H2.
Proof.
  intros. subst. auto using patch_det.
Qed.

(* Notorious part of Coq notation: the notation defined in above record is not visible at outside*)
(* Print Visibility. *)
Global Infix "↪" := (vc)(at level 60) : change_scope.
Global Notation "⟦ Δx ⟧" := (patch Δx).
Global Notation "t ⊕ Δt" := (⟦ Δt ⟧ t _)
  (at level 10, Δt at level 20, left associativity) : change_scope.
Global Notation "t ⊕ Δt ~ v" := (patch Δt t v)
  (at level 10, Δt at level 20, v at level 20, left associativity) : change_scope.


Program Definition repl_change A : change A := {|
    ΔT := A
  ; vc _ _ := True  
  ; patch new old _ := new
|}.


Module Difference. (* In the future, we can move it a separate file. *)
Reserved Infix "⊖" (at level 10, left associativity).

Structure difference T : Type := {
    cdiff : change T
  ; diff : T -> T -> cdiff.(ΔT)
      where "new ⊖ old" := (diff old new) : change_scope
  (* ; diff : forall t1 t2, raw_diff t1 t2 ↪ t2   *)
  ; valid_diff : forall new old, (new ⊖ old) ↪ old
  ; patch_diff : forall new old H, old ⊕ (new ⊖ old) ~ H = new
}.

Arguments diff [T].
Arguments valid_diff [T].
Arguments patch_diff [T].
Notation "new ⊖ old" := (diff _ old new)(at level 10, left associativity) : change_scope.

Lemma diff_patch_noc : forall T {D : difference T} (t : T) H , 
  t ⊕ (diff D t t) ~ H = t.
Proof. intros. rewrite patch_diff. auto. Qed.
End Difference. 

Global Hint Resolve patch_det : core.
