From Stdlib Require Import List Lia PeanoNat Nat.
From AUTOINC Require Import Change Operator Partial NatChange Tactic BoolChange PairChange SeqChange EqDec.
Import NatChange BoolChange PairChange SeqChange.
Local Open Scope change_scope.

Ltac patch_tac := 
  simpl in *;
  repeat match goal with
  | [H : nat_vc ?k ?st |- context [nat_patch ?k ?st]] => x_inv H
  | [H : seq_vc ?k ?st |- context [seq_patch ?k ?st]] => x_inv H
  | [H : pair_vc ?k ?st |- context [pair_patch ?k ?st]] => x_inv H
  | [H : bool_vc ?k ?st |- context [bool_patch ?k ?st]] => x_inv H
  end; auto 3.

Ltac nat_vc_tac := 
  simpl in *;
  repeat match goal with
  | [H : match ?Δx with
        | nat_add _ => _
        | nat_minus _ => _
        end _ |- _] => destruct Δx eqn:?
  end; auto 3.

Hint Extern 4 => simpl nat_patch : core.
Hint Extern 4 => simpl seq_patch : core.
Hint Extern 4 => econstructor : core.
Hint Extern 4 => discriminate : core.
Hint Extern 4 => lia : core.
Hint Extern 4 => nia : core.


Module IncrementOp <: StatelessDiffOp.
  Definition A := nat.
  Definition B := nat.

  Definition CA := natc.
  Definition CB := natc.
  Definition Δnat := CA.(ΔT).

  Definition f (x: A) : B := S x.

  Definition Δf (c : Δnat) : Δnat := c.

  Lemma inc_valid : forall x Δx,
    vc Δx x -> vc (Δf Δx) (f x).
  Proof. 
    intros. nat_vc_tac.
  Qed.

  Hint Extern 4 => unfold f : core.
  Hint Extern 4 => unfold Δf : core.

  Lemma inc_correct : forall x Δx (vcx : vc Δx x) vcy,
    f (patch Δx x vcx) = patch (Δf Δx) (f x) vcy.
  Proof.
    intros. unfold Δf in *. nat_vc_tac. destruct n; auto. 
  Qed.
End IncrementOp.

Module DoubleOp <: StatelessDiffOp.
  Definition A := nat.
  Definition B := nat.
  Definition CA := natc.
  Definition CB := natc.
  Definition Δnat := CA.(ΔT).

  Definition f (x: A) : B := 2 * x.

  Definition Δf (c : Δnat) : Δnat :=
    match c with
    | nat_add k => nat_add (2 * k)
    | nat_minus k => nat_minus (2 * k)
    end.

  Hint Extern 4 => unfold f : core.
  Hint Extern 4 => unfold Δf : core.


  Lemma inc_valid : forall x Δx,
    vc Δx x -> vc (Δf Δx) (f x).
  Proof. 
    intros. nat_vc_tac.
  Qed.

  Lemma inc_correct : forall x Δx (vcx : vc Δx x) vcy,
    f (patch Δx x vcx) = patch (Δf Δx) (f x) vcy.
  Proof.
    intros. unfold Δf. simpl. nat_vc_tac.
  Qed.
End DoubleOp.

Module EvenOp <: StatelessDiffOp.
  Definition A := nat.
  Definition B := bool.
  Definition CA := natc.
  Definition CB := boolc.
  Definition Δnat := CA.(ΔT).
  Definition Δbool := CB.(ΔT).

  Definition f := Nat.even.

  Definition Δf (c : Δnat) : Δbool :=
    match c with
    | nat_add k => if Nat.even k then bool_noc else bool_neg
    | nat_minus k => if Nat.even k then bool_noc else bool_neg
    end.

  Hint Extern 4 => unfold f : core.
  Hint Extern 4 => unfold Δf : core.

  Lemma inc_valid : forall x Δx,
    vc Δx x -> vc (Δf Δx) (f x).
  Proof. intros. nat_vc_tac. Qed.

  Hint Extern 4 => rewrite Nat.even_add : core.
  Hint Extern 4 => rewrite Nat.even_sub : core.


  Lemma inc_correct : forall x Δx (vcx : vc Δx x) vcy,
    f (patch Δx x vcx) = patch (Δf Δx) (f x) vcy.
  Proof.
    intros. nat_vc_tac; unfold f.
    - rewrite Nat.even_add. simpl in *.
      destruct (Nat.even n) eqn:EEn; destruct (Nat.even x) eqn:EEx; auto. 
    - rewrite Nat.even_sub; auto. simpl in *.
      destruct (Nat.even n) eqn:EEn; destruct (Nat.even x) eqn:EEx; auto. 
  Qed.
End EvenOp.


Module SquareInputOp <: InputDiffOp.
  Definition A := nat.
  Definition B := nat.
  (* Definition EqA := EqDec.nat_EqDec.
  Definition EqB := EqDec.nat_EqDec. *)
  Definition CA := natc.
  Definition CB := natc.

  Definition f x := x * x.

  Definition Δf (Δx : ΔT CA) (x : nat) (_ : vc Δx x) : ΔT CB :=
  match Δx with
  | nat_add k => nat_add (2 * k * x + k * k)
  | nat_minus k => nat_minus (2 * x * k - k * k)
  end.

  Lemma inc_valid : forall Δx x vcx, vc (Δf Δx x vcx) (f x).
  Proof.
    unfold Δf. unfold f. intros. nat_vc_tac.
  Qed.  
  
  Lemma inc_correct : forall Δx x vcx vcy, 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx x vcx ~ vcy.
  Proof.
    unfold Δf. unfold f. intros. subst. nat_vc_tac; try injection Heqn; auto.
  Qed. 
  
End SquareInputOp.

Module SquareOP := InputDiffOpFunctor(SquareInputOp).

(* Module AddOp <: SLCommOP.
  Definition A := nat.
  Definition B := nat.
  Definition CA := natc.
  Definition CB := natc.
  Definition Δnat := natc.(ΔT).

  Definition f x y := x + y.

  Definition Δf (c : Δnat) : Δnat :=
    match c with
    | nat_add k => nat_add k
    | nat_minus k => nat_minus k
    end.

  Hint Extern 4 => unfold f; unfold Δf : core.

  Lemma f_comm : forall x y, f x y = f y x.
  Proof. unfold f. lia. Qed.

  Lemma inc_valid : forall x y Δ,
    Δ ↪ x -> Δf Δ ↪ f x y.
  Proof. intros x y Δx H. x_inv H; auto. Qed.

  Lemma inc_correct : forall x y Δ vCA vCB,
    f (x ⊕ Δ ~ vCA) y = f x y ⊕ Δf Δ ~ vCB.
  Proof. intros. inversion vCA; subst; unfold f; simpl; auto. Qed.

End AddOp. *)

(* Module MulOp <: SFCommOP.
  Definition A := nat.
  Definition B := nat.
  Definition CA := natc.
  Definition CB := natc.
  Notation Δnat := natc.(ΔT).
  Definition f x y := x * y.
  
  Definition Δf (c : Δnat) (other : A) : Δnat := 
    match c with
    | nat_add k => nat_add (k * other)
    | nat_minus k => nat_minus (k * other)
    end.

  Hint Extern 4 => unfold f in *; unfold Δf in * : core.

  Hint Extern 4 => lia : core.

  Lemma f_comm : forall x y, f x y = f y x.
  Proof. unfold f; lia. Qed.

  Lemma inc_valid : forall x y Δ,
    Δ ↪ x -> Δf Δ y ↪ f x y.
  Proof. intros. inversion X; subst; auto. Qed.

  Lemma inc_correct : forall x y Δ vCA vCB,
    f (x ⊕ Δ ~ vCA) y = f x y ⊕ Δf Δ y ~ vCB.
  Proof. unfold f. intros. inversion vCA; subst; simpl; auto 1. Qed.

End MulOp. *)

(* Module SubOp <: StatefulInc.
  Definition A : Type := nat * nat.
  Definition B := nat.
  Definition CA := pairc natc natc.
  Definition CB := seqc natc.
  Definition Δpair := CA.(ΔT).
  Definition Δseq := CB.(ΔT).
  Definition Δnat := natc.(ΔT).

  Definition f p := let '(x,y) := p in x - y.

  Inductive ST : Type := 
  | Pos (d : nat)
  | Neg (d : nat).
  
  Definition mkST (p : A) : ST := 
    let '(x,y) := p in 
    if Nat.leb x y then Neg (y - x) else Pos (y - x).
  Definition inv (p : A) (st : ST) := st = mkST p.
  Definition vs (dx : Δpair) (st : ST) := True.

  Definition Δf1 (c : Δnat) (st : ST) : Δnat * ST := 
    match c with
    | nat_noc => (nat_noc, st)
    | nat_add k => nat_add (k * other)
    | nat_minus k => nat_minus (k * other)
    end.

  Equations Δf (c : Δpair) (st : A) (vsc : vs c st) : Δseq * A :=
    | pair_noc, st, vsc => (nil_change, patch pair_noc st vsc)
    | pair_fst dx, st, vsc => (cons_change (Δfn dx (snd st)) nil_change, patch (pair_fst dx) st vsc)
    | pair_snd dy, st, vsc => (cons_change (Δfn dy (fst st)) nil_change, patch (pair_snd dy) st vsc)
    | pair_both dx dy, st, vsc => 
      let CA := Δfn dy (fst st) in
      let CB := Δfn dx (patch dy (snd st) _) in
      (cons_change CA (cons_change CB nil_change), patch (pair_both dx dy) st vsc).

  Transparent Δf.
  Hint Extern 4 => unfold f; unfold Δfn : core.

  Lemma state_valid : forall x Δx st,
    inv x st -> vc Δx x -> vs Δx st.
  Proof. intros. x_inv H. trivial. Qed.


  Lemma inv_step : forall x Δx st vcx vsx Δy st',
    Δf Δx st vsx = (Δy, st') -> inv x st -> inv (patch Δx x vcx) st'.
  Proof.
    intros. unfold inv in *. subst.
    funelim (st ⊕ Δx); simpl in *; x_inj; auto.
  Qed.      
      
  Lemma inc_valid : forall x y Δx st vsx Δy st', 
    f x = y -> vc Δx x -> inv x st -> Δf Δx st vsx = (Δy, st') -> vc Δy (f x).
  Proof.
    intros. unfold inv in *. subst.     
    inversion H0; subst; simp Δf in H2; try x_inj; try injection H2 as H2; subst; try x_inj; auto.
  Unshelve. all: nat_vc_tac. Qed. 


  Lemma inc_correct : forall x y Δx st vcx vsx Δy st' vcy, 
    f x = y -> inv x st -> Δf Δx st vsx = (Δy, st') -> 
      f (patch Δx x vcx) = patch Δy (f x) vcy.
  Proof.
    unfold f in *. unfold inv in *. intros. destruct x as [x1 x2]. destruct st as [sA sB]. patch_tac.  
  Qed.
End MulOp. *)
