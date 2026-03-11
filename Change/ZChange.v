From AUTOINC Require Import Change.
From Stdlib Require Import ZArith.

Section ZChange.
  Inductive z_change : Type :=
  | z_noc : z_change
  | z_incr : Z -> z_change
  | z_decr : Z -> z_change.

  Inductive z_vc : z_change -> Z -> Type :=
  | z_vc_all : forall Δt t, z_vc Δt t.

  Definition z_patch (Δt : z_change) (t : Z) : Z := 
    match Δt with
    | z_noc => t
    | z_incr t' => t + t'
    | z_decr t' => t - t'
    end.
  

  Program Definition zc : change Z := 
  {| ΔT := z_change
   ; vc := z_vc
   ; patch Δt t v := z_patch Δt t
  |}.

  Program Definition unit_z : unit Z :=
  {| cunit := zc
  ;  noc   := z_noc
  |}.
  Next Obligation. constructor. Defined.
    
End ZChange.


