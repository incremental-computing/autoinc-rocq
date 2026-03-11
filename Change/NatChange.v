From AUTOINC Require Import Change EqDec Tactic.
From Stdlib Require Import Arith.PeanoNat Compare_dec Lia.
Open Scope nat_scope.

Section NatChange.
  Import Difference.
  Inductive nat_change :=
  | nat_add : nat -> nat_change
  | nat_minus : nat -> nat_change.

  Inductive nat_vc : nat_change -> nat -> Type :=
  | vc_nat_add : forall n a, nat_vc (nat_add a) n
  | vc_nat_minus : forall n m, m <= n -> nat_vc (nat_minus m) n.
  
  Definition nat_patch Δt t : nat := 
    match Δt with
    | nat_add m => t + m
    | nat_minus m => t - m
    end.

  Definition nat_repl (n1 n2 : nat) : nat_change :=
    if le_dec n1 n2
    then nat_add (n2 - n1)
    else nat_minus (n1 - n2).


  Lemma nat_vc_repl : forall n1 n2, nat_vc (nat_repl n1 n2) n1.
  Proof. intros. unfold nat_repl. dest_match; constructor. lia. Qed.


  Lemma nat_patch_repl : forall n1 n2, 
    nat_patch (nat_repl n1 n2) n1 = n2.
  Proof. intros. unfold nat_repl; dest_match; simpl; lia. Qed. 

  Hint Extern 4 => constructor : core.
  Hint Extern 4 => apply nat_vc_repl : core.
  Hint Extern 4 => apply nat_patch_repl : core.

  Program Definition natc : change nat :=
  {| ΔT := nat_change
   ; vc c n := match c with
     | nat_add k => True
     | nat_minus k => k <= n
     end
   ; patch c n _ := match c with
     | nat_add k => n + k
     | nat_minus k => n - k
   end
  |}.
    
  Hint Extern 4 => lia : core.
  Hint Extern 4 => discriminate : core.

  Program Definition NatDiff : difference nat  := 
  {| cdiff := natc 
  ; diff x y := if lt_dec x y then nat_add (y - x) else nat_minus (x - y)
  |}.
  Next Obligation.
    intros. destruct old, new; dest_match; simpl; auto; dest_match; try x_inj; auto.
  Defined.
  Next Obligation.
    intros. destruct old, new; simpl in *; dest_match; try x_inj; auto.
  Defined. 
End NatChange.

From Stdlib Require Import ZArith.
Program Definition intc : change Z :=
{| ΔT := Z
  ; vc c n := True
  ; patch c n _ := Z.add n c
|}.
