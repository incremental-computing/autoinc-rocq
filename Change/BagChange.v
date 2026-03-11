From Stdlib Require Import Compare_dec FunctionalExtensionality Eqdep.
From AUTOINC Require Import EqDec ListBag Change.

Set Implicit Arguments.

Local Open Scope bag_scope.



Section BagChange.
  Variable T : Type.
  Context `{EqT : EqDec T}.
  (* TODO : higher-order bag change, the change to the multiplicity of each element in the bag.
  *)
  Inductive bag_change : Type :=
  | bag_union : bag T -> bag_change
  | bag_diff : bag T -> bag_change
  .

  (* Not important, as we will replace bag to finite map (equality decidable) in the future. *)
  Instance bag_change_eq_dec : EqDec bag_change.
  Proof.
    unfold EqDec.
    decide equality; auto; apply list_EqDec; auto.
  Defined.


  Inductive bag_vc : bag_change -> bag T -> Prop :=
  | vc_bag_union : forall b b', bag_vc (bag_union b') b
  | vc_bag_diff : forall b b', b' ⊆ b -> bag_vc (bag_diff b') b
  .

  Definition bag_patch Δt t : bag T :=
    match Δt with
    | bag_union b => union_all t b
    | bag_diff b => diff_bag t b
    end.

  Local Obligation Tactic := try constructor.

  Program Definition bagc : change (bag T) := {|
    ΔT := bag_change
  ; vc Δb b := match Δb with
    | bag_union s => True
    | bag_diff s => s ⊆ b
  end
  ; patch Δb b _ := match Δb with
    | bag_union s => union_all b s
    | bag_diff s => diff_bag b s
    end
  |}.

  (* Program Definition unit_bag : unit (bag T) := {|
    cunit := bagc
  ; noc := bag_noc
  |}. *)
End BagChange.



