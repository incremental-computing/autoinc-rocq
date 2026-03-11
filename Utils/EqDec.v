From Stdlib Require Import PeanoNat Bool List.

Class EqDec A := 
  eq_dec : forall (x y : A), {x = y} + {x <> y}.


Ltac dest_eq_dec :=
  let tac eq := fun x y => destruct (eq x y); 
    subst; simpl in *; 
    try easy in
    repeat match goal with
    | [H : _ * _ |- _] => destruct H
    | [H : EqDec _, H' : context[if (?H ?x ?y) then _ else _] |- _] => 
    tac H x y
    | [H : EqDec _ |- context [if (?H ?x ?y) then _ else _]] =>
    tac H x y
    end.

Ltac eq_dec_auto := unfold EqDec; repeat decide equality.

Global Instance bool_EqDec : EqDec bool := {
  eq_dec := bool_dec
}.

Global Instance nat_EqDec : EqDec nat := {
  eq_dec := PeanoNat.Nat.eq_dec
}.

Global Instance list_EqDec A `{EqA : EqDec A} : EqDec (list A) := {
  eq_dec := @list_eq_dec A EqA
}.

Global Instance prod_EqDec A B `{EqA : EqDec A} `{EqB : EqDec B} : EqDec (A * B).
Proof. red. decide equality. Defined.


Ltac prod_eq_tac A_EqDec B_EqDec :=
  try eapply prod_EqDec; try eapply A_EqDec; try eapply B_EqDec.