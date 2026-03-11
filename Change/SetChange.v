From AUTOINC Require Import EqDec Change Tactic.
From Stdlib Require Import List.

Section SetChange.
  Variable A : Type.
  Context `{EqA : EqDec A}.

  Inductive set_change :=
  | set_noc
  | set_ins : A -> set_change
  | set_del : A -> set_change
  .

  Definition set T := {l : list T | NoDup l}.

  Definition In_set {T} (a : T) (s : set T) : Prop :=
    In a (proj1_sig s).
  
  Lemma NoDup_remove : forall l a,
    NoDup l -> NoDup (remove EqA a l).
  Proof.
    induction l; intros; simpl; auto; x_inv H.
    dest_match; auto. constructor; auto. intro c. apply in_remove in c. firstorder.
  Qed.

  Local Obligation Tactic := intros; subst; simpl in *; auto.
  Program Definition setc : change (set A) := {|
    ΔT := set_change
  ; vc c s := 
      match c with
      | set_noc => True
      | set_ins a => not (In_set a s)
      | set_del a => In_set a s
      end
  ; patch c s H := 
      match c with
      | set_noc => s
      | set_ins a => a :: s
      | set_del a => remove _ a s
      end
  |}.
  Next Obligation. constructor; auto; apply proj2_sig. Qed.
  Next Obligation. apply NoDup_remove. apply proj2_sig. Qed.
  Next Obligation. destruct dt; auto; apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat; auto. Qed.

  
End SetChange.



