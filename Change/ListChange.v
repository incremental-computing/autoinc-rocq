(* From AUTOINC Require Import Change NatChange EqDec Tactic.
From Stdlib Require Import Lia Arith.PeanoNat Lists.List Program.Equality.
Import ListNotations.

Section ListChange.
  Variable A : Type.
  Context `{EqA : EqDec A}.
  
  Inductive list_change :=
  | list_noc : list_change
  | list_insert : nat -> A -> list_change
  | list_delete : nat -> A -> list_change
  .

  Program Fixpoint nth_safe (l : list A) i : i < length l -> A :=
    match l with
    | [] => _
    | hd :: tl => fun pf => match i with
                  | O => hd 
                  | S i => nth_safe tl i (PeanoNat.lt_S_n i (length tl) pf)
                  end
    end.
  Next Obligation.
    lia.
  Defined.

  Lemma nth_th : forall l i H1 H2,
    nth_safe l i H1 = nth_safe l i H2. 
  Proof.
    induction l; intros.
    - simpl in *; lia.
    - simpl; destruct i; auto. 
  Qed.

  Inductive list_vc_p : list_change * list A -> Type :=
  | vc_list_noc : forall l, list_vc_p (list_noc, l)
  | vc_list_insert : forall l i a (H : i <= length l), list_vc_p (list_insert i a, l)
  | vc_list_delete : forall l i a (H : i < length l) (H' : nth_safe l i H = a), list_vc_p (list_delete i a, l)
  .

  #[export] Instance list_change_EqDec : EqDec list_change.
  Proof.
    eq_dec_auto.
  Defined.

  Hint Extern 4 => simple apply prod_EqDec : core.
  Hint Extern 4 => simple apply list_change_EqDec : core.
  Hint Extern 4 => decide equality; auto : core.
  Hint Extern 4 => lia : core.

  Lemma list_vc_case : forall c l (P : list_vc_p (c, l) -> Type),
    (forall (pf : list_noc = c), 
      P (eq_rect list_noc (fun s => list_vc_p (s, l)) (vc_list_noc l) c pf)) ->
    (forall i a H (pf : list_insert i a = c), 
      P (eq_rect (list_insert i a) (fun s => list_vc_p (s, l)) (vc_list_insert l i a H) c pf)) ->
    (forall i a H H' (pf : list_delete i a = c), 
      P (eq_rect (list_delete i a) (fun s => list_vc_p (s, l)) (vc_list_delete l i a H H') c pf)) ->
    forall v, P v.
  Proof.
    intros.
    refine (
        match v as v' in list_vc_p (Δk, k) return 
          (forall (pf1 : (Δk, k) = (c, l)),
            eq_rect (Δk, k) list_vc_p v' (c, l) pf1 = v ->
            P v
        ) with
        | vc_list_noc _ => _
        | vc_list_insert _ _ _ _ => _
        | vc_list_delete _ _ _ _ _ => _
        end eq_refl eq_refl
    ); intros; rewrite <- H; inversion pf1; subst; rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
    - specialize (X eq_refl); auto.
    - specialize (X0 n a l1 eq_refl); auto.
    - specialize (X1 n (nth_safe l n l1) l1 eq_refl eq_refl); auto.
  Qed.

  Definition list_vc Δt t : Type := list_vc_p (Δt, t).

  Program Fixpoint insert_patch (l : list A) i (a : A) : i <= length l -> list A :=
    match l with
    | [] => fun _ => match i with
                      | O => [a]
                      | S _ => _
                      end
    | hd :: tl => fun _ => match i with
                  | O => a :: hd :: tl
                  | S i =>  hd :: (insert_patch tl i a (le_S_n i (length tl) _))
                  end
    end.
  Next Obligation.
    lia.
  Defined.

  Lemma insert_patch_pir : forall l i a H1 H2,
    insert_patch l i a H1 = insert_patch l i a H2.
  Proof.
    induction l; intros; destruct i; simpl in *; try f_equal; auto.
  Qed.

  Program Fixpoint delete_patch l i : i < @length A l -> list A :=
    match l with
    | [] => _
    | hd :: tl => fun pf => match i with
                  | O => tl 
                  | S i => hd :: delete_patch tl i _
                  end
    end.
  Next Obligation.
    lia.
  Defined.

  Transparent delete_patch.

  Lemma delete_patch_pir : forall l i H1 H2,
    delete_patch l i H1 = delete_patch l i H2.
  Proof.
    induction l; intros. 
    - simpl in H1; lia.
    - destruct i; simpl; try f_equal; auto. 
  Qed. 

  Definition list_patch Δt t (vc : list_vc Δt t) : list A := 
    match vc with
    | vc_list_noc t => t
    | vc_list_insert l i a H => insert_patch l i a H
    | vc_list_delete l i a H H' => delete_patch l i H
    end.

  Hint Extern 4 => apply insert_patch_pir : core.
  Hint Extern 4 => apply delete_patch_pir : core.
  
  Lemma list_patch_pir : forall Δt t vc1 vc2, list_patch Δt t vc1 = list_patch Δt t vc2.
  Proof.
    intros.  dest_duo_patch vc1 vc2 list_vc_case pf.
    rewrite <- pf. 
    rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
  Qed.

  Hint Resolve list_patch_pir : core.
  
  Program Definition listc : change (list A) := 
  {| ΔT := list_change
   ; vc := list_vc
   ; patch := list_patch
  |}.

  Local Obligation Tactic := constructor.
  Program Definition unit_clist : unit (list A) := 
  {| cunit := listc
   ; noc := list_noc
  |}.
  
End ListChange.


Arguments list_noc {A}.
Arguments list_insert [A].
Arguments list_delete [A].
Arguments list_patch [A].
Arguments delete_patch [A].
Arguments list_vc [A].
Arguments list_vc_p [A].


Arguments vc_list_noc {A}.
Arguments vc_list_insert [A].
Arguments vc_list_delete [A].
 *)
