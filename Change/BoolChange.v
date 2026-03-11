From AUTOINC Require Import Change.

Section BoolChange.
  Inductive bool_change :=
  | bool_noc  : bool_change
  | bool_neg  : bool_change
  .
  Definition bool_vc (Δt : bool_change) (t : bool) : Prop := True.
  
  Definition bool_patch Δt t : bool :=
  match Δt with
  | bool_noc => t
  | bool_neg => negb t
  end.

  Transparent bool_patch.

  Definition bool_repl (b1 b2 : bool) : bool_change :=
    match (b1, b2) with
    | (true, true) => bool_noc
    | (false, true) => bool_neg
    | (true, false) => bool_neg
    | (false, false) => bool_noc
    end.


  Program Definition boolc : change bool := {|
    ΔT := bool_change
  ; vc := bool_vc
  ; patch Δt t _ := bool_patch Δt t
  |}.
  

  (* Program Definition unit_bool : unit bool := {|
    cunit := boolc
  ; noc := bool_noc
  |}.
  Next Obligation. constructor. Defined. *)


End BoolChange.


