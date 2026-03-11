From Stdlib Require Import Classes.SetoidClass.
From Stdlib Require Import Lists.List.
Import ListNotations.


#[export, refine] Instance option_Setoid {A} `{Setoid A} : Setoid (option A) :=
{
  equiv a b := match a, b with
  | None, None => True
  | Some a, Some b => a == b
  | _, _ => False
  end
}.
Proof.
  split. 
  - unfold Reflexive; intros. destruct x; reflexivity.
  - unfold Symmetric; intros; destruct x; destruct y; auto. symmetry; auto.
  - unfold Transitive; intros; destruct x; destruct y; destruct z; auto.
    setoid_transitivity a0; auto. contradiction.
Defined.

Global Ltac dest_match := repeat match goal with
| _ : context [match ?adt with _ => _ end] |- _ => destruct adt eqn:?EQ; subst
| |- context [match ?adt with _ => _ end] => destruct adt eqn:?EQ; subst
| |- context [if ?E then _ else _] => destruct E eqn:?EQ; subst
end.

Global Ltac x_inj := 
let H := fresh "H" in
match goal with
| [H : ?V ?x = ?V ?y |- _] => injection H as H; subst
| [H : ?V ?x ?y = ?V ?x ?y |- _] => injection H as H; subst
| [H : (_, _) = (_, _) |- _] => injection H as H; subst
end.

Global Ltac if_resolve := match goal with 
| H1 : ?E = false, H2 : context [if ?E then _ else _] |- _  =>
  rewrite H1 in H2; simpl in H2
| H1 : ?E = true, H2 : context [if ?E then _ else _] |- _  =>
  rewrite H1 in H2; simpl in H2
end. 
  
Global Ltac match_resolve := match goal with 
| H1 : ?E = _, H2 : context [match ?E with _ => _ end ] |- _  =>
  rewrite H1 in H2; simpl in H2
| H1 : _ = ?E, H2 : context [match ?E with _ => _ end ] |- _  =>
  rewrite <- H1 in H2; simpl in H2
end. 

Global Ltac x_inv H := inversion H; try clear H; simpl in *; subst; simpl in *; try x_inj; simpl in *.

Global Ltac x_dest := 
  let H := fresh "H" in
  repeat match goal with
  | [H : _ \/ _ |- _] => destruct H as [H | H]
  | [H : _ /\ _ |- _] => destruct H as [? ?]
  end.

Global Ltac x_ind t := induction t; simpl; intros; dest_match; auto.

(* rewrite an equation on both sides. *)
Global Ltac rew_both H := rewrite H; [symmetry; rewrite H; [symmetry | ..] | ..].