(* Signatures for various kinds of incremental operators. *)
From AUTOINC Require Import Change PairChange SeqChange.
From Stdlib Require Import Classes.SetoidClass.

Module Type SetoidStatelessDiffOp.
  (**
  Stateless incremental operator:
  Given a normal operator 
        f : T1 -> T2, 
  a stateless operator Δf : ΔT1 -> ΔT2 ought to 
  produce a correct output change to the output solely 
  based on the input change, s.t.
  f (t ⊕ Δt1) = (f t) ⊕ (Δf Δt1)
  *)

  Parameter A B : Type.
  
  #[local] Parameter SoB : Setoid B.
  Existing Instance SoB.

  Parameter CA : change A.
  Parameter CB : change B.

  Notation ΔTA := CA.(ΔT).
  Notation ΔTB := CB.(ΔT).
  
  Parameter f : A -> B. (* original function *)
  
  Parameter Δf : ΔTA -> ΔTB. (* incremental function *)
  
  Axiom inc_valid : forall x Δx, Δx ↪ x -> Δf Δx ↪ f x.

  Axiom inc_correct : forall x Δx vcx,
    f (x ⊕ Δx ~ vcx) == f x ⊕ Δf Δx ~ (inc_valid x Δx vcx).

End SetoidStatelessDiffOp.

Module Type SetoidStatefulDiffOp.
  (**
  Stateful incremental operators:
  Given a normal operator 
        f : T1 -> T2, 
  a stateful operator Δf : ΔT1 -> ST -> ΔT2 * ST maintains a state st and 
  keeps the following specification during incrementalization, where 
  `inv` is an invariant that ensures the state is compatible with the latest 
  input to f.

  - output is correct : inv t st -> f (t ⊕ Δt) = f t ⊕ (Δf Δt st)._1
  - state is updated correctly : inv t st -> inv (t ⊕ Δt) (Δf Δt st)._2

  *)

  Parameter A B : Type.
  #[local] Parameter SoB : Setoid B.
  Existing Instance SoB.
  Parameter CA : change A.
  Parameter CB : change B.  
  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).
  
  Parameter f : A -> B. (* original function *)

  Parameter ST : Type. (* state of incremental function *)

  Parameter inv : A -> ST -> Prop.

  Parameter vs : ΔA -> ST -> Prop.

  Parameter Δf : forall Δt st, vs Δt st -> ΔB. 
  Parameter Δst : forall Δt st, vs Δt st -> ST. 
  Parameter init : A -> ST.
  Axiom state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Axiom inv_init : forall x, inv x (init x). 
  Axiom inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).

  Axiom inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.
  
  Axiom inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) == f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).

End SetoidStatefulDiffOp.


