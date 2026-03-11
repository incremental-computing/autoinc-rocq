From Stdlib Require Import Ascii List.
From AUTOINC Require Import Change SeqChange Tactic.

Set Implicit Arguments.
Notation string := (list ascii).

Section StringChange.
  
  Inductive str_change :=
    | str_noc : str_change
    | str_prepend : ascii -> str_change
    | str_append : ascii -> str_change
    .

  Definition str_vc (_ : str_change) (_ : list ascii) : Prop :=
    True.

  Definition str_patch Δt t:=
    match Δt with
    | str_noc => t
    | str_prepend a => cons a t
    | str_append a => (t ++ (cons a nil))%list
    end.

  Program Definition stringc : change string := {|
    ΔT := str_change
  ; vc := str_vc
  ; patch Δt t v := str_patch Δt t
  |}.


End StringChange.

Local Hint Extern 4 => constructor : core.
(* A sequence of string change can be applied to any change. *)
Lemma str_change_free : forall (l : seq_change stringc), list_vc_free l.
Proof.
  unfold list_vc_free, vc_free.
  x_ind l.
Qed.

Hint Resolve str_change_free seq_vc_free : core.

Inductive all_append_seq : seq_change stringc -> Prop :=
| all_append_seq_nil : all_append_seq nil
| all_append_seq_cons s a Δx : Δx = str_append a -> all_append_seq s -> all_append_seq (str_append a :: s).


Lemma str_append_seq : forall (l : seq_change stringc) t v1 v2,
  all_append_seq l -> seq_patch stringc l t v1 = t ++ seq_patch stringc l nil v2.
Proof.
  x_ind l. rewrite app_nil_r. auto.
  inversion H; subst; simpl. erewrite IHl; auto.
  simpl.
  erewrite seq_patch_pir. symmetry. erewrite seq_patch_pir.
  erewrite IHl; eauto.
  rewrite app_assoc. auto.
  Unshelve. all: auto. 
Qed. 
