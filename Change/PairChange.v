From AUTOINC Require Import Change Tactic EqDec.
From Stdlib Require Import Eqdep.

Section PairChange.
  Variable (A : Type) (B : Type).
  Variable (CA : change A) (CB : change B).

  Notation ΔA := CA.(ΔT).
  Notation ΔB := CA.(ΔT).

  Inductive pair_change : Type :=
  | pair_fst  : CA.(ΔT) -> pair_change
  | pair_snd  : CB.(ΔT) -> pair_change
  | pair_both : CA.(ΔT) -> CB.(ΔT) -> pair_change.

  Inductive pair_vc : pair_change -> A * B -> Prop :=
  | vc_pair_fst : forall t1 t2 Δt1, Δt1 ↪ t1 -> pair_vc (pair_fst Δt1) (t1, t2)
  | vc_pair_snd : forall t1 t2 Δt2, Δt2 ↪ t2 -> pair_vc (pair_snd Δt2) (t1, t2)
  | vc_pair_both : forall t1 t2 Δt1 Δt2,
      Δt1 ↪ t1 -> Δt2 ↪ t2 -> pair_vc (pair_both Δt1 Δt2) (t1, t2).


  (* Lemma pair_vc_case : forall c t1 t2 (P : pair_vc_p (c, (t1, t2)) -> Type),
    (forall k v pf, 
      P (eq_rect (pair_fst k) (fun s => pair_vc_p (s, (t1, t2))) (vc_pair_fst t1 t2 k v) c pf)) ->
    (forall k v pf, 
      P (eq_rect (pair_snd k) (fun s => pair_vc_p (s, (t1, t2))) (vc_pair_snd t1 t2 k v) c pf)) ->
    (forall k1 k2 v1 v2 pf, 
      P (eq_rect (pair_both k1 k2) (fun s => pair_vc_p (s, (t1, t2))) (vc_pair_both t1 t2 k1 k2 v1 v2) c pf)) ->
    forall v, P v.
  Proof.
    intros. 
    refine (
      match v as v' in (pair_vc_p (Δk, k)) return
        forall (pf1 : (Δk, k) = (c, (t1, t2))),
        eq_rect (Δk, k) pair_vc_p v' (c, (t1, t2)) pf1 = v ->
        P v
      with
      | vc_pair_fst t1 t2 c vct1 => _
      | vc_pair_snd t1 t2 c vct2 => _
      | vc_pair_both t1 t2 c1 c2 vct1 vct2  => _
      end eq_refl eq_refl); 
    intros pf1 Heq; inversion pf1; subst; rewrite <- eq_rect_eq; auto.
    - specialize (X0 c vct1 eq_refl); auto.
    - specialize (X1 c vct2 eq_refl); auto.
    - specialize (X2 c1 c2 vct1 vct2 eq_refl); auto.
  Qed.
   *)
  Program Definition pair_patch c p (vc : pair_vc c p) : A * B := 
    match c with
    | pair_fst ca => (patch ca (fst p) _, (snd p))
    | pair_snd cb => (fst p, patch cb (snd p) _)
    | pair_both ca cb  => (patch ca (fst p) _, patch cb (snd p) _)
    end.
  Next Obligation. inversion vc; subst; auto. Defined.
  Next Obligation. inversion vc; subst; auto. Defined.
  Next Obligation. inversion vc; subst; auto. Defined.
  Next Obligation. inversion vc; subst; auto. Defined.
  
  

  Hint Extern 4 => constructor : core.
  Hint Extern 4 => erewrite patch_det : core.

  Lemma pair_patch_pir_dep : forall Δt1 Δt2 t1 t2 vc1 vc2,
    Δt1 = Δt2 -> t1 = t2 -> pair_patch Δt1 t1 vc1 = pair_patch Δt2 t2 vc2.
  Proof.
    induction Δt1; simpl; intros; subst; destruct t2; simpl; eauto.
    f_equal.
    erewrite patch_det. eauto.
    erewrite patch_det. eauto.
    Unshelve. all: inversion vc1; inversion vc2; subst; auto. 
  Qed.
  Hint Resolve pair_patch_pir_dep : core. 
  Lemma pair_patch_pir : forall Δt t vc1 vc2, 
    pair_patch Δt t vc1 = pair_patch Δt t vc2.
  Proof. eauto. Qed.
    (* intros Δt [t1 t2] vc1 vc2.
    dest_duo_patch vc1 vc2 pair_vc_case pf; f_equal; auto.
  Qed. *)

  Hint Resolve pair_patch_pir : core.

  (* Definition pair_repl (x y : T1 * T2) : pair_change :=
    let '(x1, x2) := x in
    let '(y1, y2) := y in
    pair_both (CT1.(repl) x1 y1) (CT2.(repl) x2 y2). *)
  (* Transparent pair_repl. *)

  (* Hint Extern 4 => apply vc_repl : core. *)
  (* Hint Extern 4 => apply patch_repl : core. *)

  Local Obligation Tactic := intros; try (subst; auto; firstorder; fail).
  Program Definition pairc : change (A * B) := {|
    ΔT    := pair_change;
    vc c p := match c with
      | pair_fst ca => vc ca (fst p)
      | pair_snd cb => vc cb (snd p)
      | pair_both ca cb => vc ca (fst p) /\ vc cb (snd p)
      end;
    patch c p _ := match c with
      | pair_fst ca => (fst p ⊕ ca, snd p)
      | pair_snd cb => (fst p, snd p ⊕ cb)
      | pair_both ca cb => (fst p ⊕ ca, snd p ⊕ cb)
      end
  |}.
  Next Obligation. simpl in *. destruct dt eqn:?; f_equal; apply patch_det. Qed.
  
  (* Program Definition unit_pair : unit (T1 * T2) := {|
    cunit := pairc
  ; noc := pair_noc
  |}.
  Next Obligation. auto. Defined. *)


  
End PairChange.

Global Transparent pair_patch.

Arguments pair_patch [A B CA CB].
Arguments pair_fst {A B CA CB}.
Arguments pair_snd {A B CA CB}.
Arguments pair_both {A B CA CB}.
Arguments pair_vc {A B CA CB}.
Arguments vc_pair_fst {A B CA CB}.
Arguments vc_pair_snd {A B CA CB}.
Arguments vc_pair_both {A B CA CB}.



Arguments pairc {A B}.

Arguments pair_vc {A B CA CB}.

(* 
Compute ((1, 2) ⊕ pair_noc).
Compute ((1, 2) ⊕ (pair_repl (1, 2) (2, 3))).
Compute ((1, 2) ⊕ (pair_fst (trivial_repl 1 2))).
Compute ((1, 2) ⊕ (pair_snd (trivial_repl 2 1))).
Compute ((1, 2) ⊕ (pair_both (trivial_repl 1 2) (trivial_repl 2 1))).

   *)
