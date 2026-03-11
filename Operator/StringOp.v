From Stdlib Require Import List Lia Compare_dec Ascii Extraction.
From AUTOINC Require Import Change Operator String Tactic List NatChange BoolChange PairChange SeqChange.
Require Import Stdlib.Program.Equality.
Import ListNotations.

Set Default Timeout 5.
(* 

for each operator:
  for each {
    short original input (len = 100 char):
    medium original input (len = 1000 char):
    long original input (len = 10000):
  }:

    short insertion/deletion (len = 1%)
    medium insertion/deletion (len = 10%)
    long insertion/deletion (len = 50%)
*)

Module ΔString.
  (*
  Changes to a string
  - noc : do nothing
  - ins (i, s): insert string s at index i
  - del (i, n): delete a string of length n at index i
  
  *)
  Inductive Δstr := 
  | noc 
  | ins (i : nat) (s : string) 
  | del (i : nat) (n : nat)
  .

  Inductive str_vc : Δstr -> string -> Prop :=
  | str_vc_noc : forall s, str_vc noc s
  | str_vc_ins : forall l n s, n <= length l -> str_vc (ins n s) l
  | str_vc_del : forall l i n, i + n <= length l -> str_vc (del i n) l
  .

  Fixpoint patch_ins i (s : string) s' := 
    match i, s with
    | 0, _ => s' ++ s
    | S i, [] => s'
    | S i, x :: s => x :: (patch_ins i s s')
    end.

  Fixpoint patch_del (s : string) i n :=
    match s, i, n with
    | nil, _, _ => nil
    | x :: xs, _, 0 => x :: xs
    | x :: xs, 0, S n => patch_del xs 0 n
    | x :: xs, S i, n => x :: patch_del xs i n
    end.

  Definition str_patch (Δs : Δstr) (s : string) :=
    match Δs with
    | noc => s
    | ins i s' => patch_ins i s s'
    | del i n => patch_del s i n
    end.


  Program Definition stringc : change string := {|
    ΔT := Δstr
  ; vc := str_vc
  ; patch Δx x _ := str_patch Δx x
  |}.


  Lemma patch_ins_empty_input : forall s i, patch_ins i [] s = s.
  Proof.
    x_ind s; destruct i; simpl in *; auto.
    rewrite app_nil_r; auto.
  Qed.

  Lemma patch_ins_empty_inserted : forall s i, patch_ins i s [] = s.
  Proof. x_ind s; destruct i; simpl; auto. Qed.

  Hint Extern 4 => lia : core.
  Hint Extern 4 => discriminate : core.


  Lemma patch_ins_length : forall s s' i, i <= length s -> length (patch_ins i s s') = length s + length s'.
  Proof.
    x_ind s; auto. rewrite patch_ins_empty_input; auto.
    destruct i, s'; simpl; auto.
    f_equal. 
    rewrite length_app; simpl; auto.
  Qed. 
    
  Lemma patch_del_length : forall s i n, i + n <= length s -> length (patch_del s i n) = length s - n.
  Proof.
    x_ind s; auto. simpl. rewrite IHs; auto.
  Qed. 

  Lemma patch_del_empty : forall s i, patch_del s i 0 = s.
  Proof. x_ind s. Qed.
  Lemma patch_ins_tail : forall s s',
    patch_ins (length s) s s' = s ++ s'.
  Proof. x_ind s; rewrite app_nil_r; auto. Qed.


  Lemma patch_ins_cons : forall s n a k,
    n <= length a ->
    patch_ins (S n) (k :: a) s = k :: patch_ins n a s.
  Proof.
    x_ind s; simpl in *; auto.
  Qed.
  Import PeanoNat.Nat.
  Ltac conv := repeat match goal with
  | |- context [length (patch_ins _ _ _)] => rewrite patch_ins_length
  | |- context [length (patch_del _ _ _)] => rewrite patch_del_length
  | |- context [length (_ ++ _)] => rewrite length_app
  | |- context [patch_ins _ _ nil] => rewrite patch_ins_empty_inserted
  | |- context [_ ++ []] => rewrite app_nil_r
  | |- context [patch_del _ _ 0] => rewrite patch_del_empty
  | |- context [_ + S _] => rewrite add_succ_r
  | |- context [patch_ins (S _) (_ :: _) _] => rewrite patch_ins_cons
  | |- context [patch_ins (length ?s) ?s _] => rewrite patch_ins_tail
  end.



  Lemma patch_ins_split : forall s i s', i <= length s -> 
    patch_ins i s s' = firstn i s ++ s' ++ skipn i s.
  Proof.
    x_ind s; destruct s'; simpl in *; auto.
    - assert (i = 0). lia. subst; auto.
    - assert (i = 0). lia. subst; auto.
    - conv. assert (Hh : i = S (length s) \/ i <= length s). lia.
      destruct Hh.
      + subst. simpl. rewrite firstn_all, skipn_all; conv; auto.
      + rewrite firstn_skipn; auto.
    - destruct i. simpl. auto.
      simpl.
      f_equal.
      rewrite IHs; auto.
  Qed.

  Lemma patch_del_split : forall s i n, i + n <= length s -> 
    patch_del s i n = firstn i s ++ skipn (i + n) s.
  Proof.
    x_ind s; simpl.
    - assert (i = 0 /\ n = 0). auto. destruct H0; subst; rewrite firstn_nil, skipn_nil; auto.
    - f_equal. replace (n0 + 0) with n0; auto. rewrite firstn_skipn; auto.
    - f_equal.
      rewrite IHs; auto.
  Qed. 
    

  Hint Extern 4 => f_equal : core.
  Lemma patch_ins_app : forall a b s n,
    n <= length a ->
    patch_ins n a s ++ b = patch_ins n (a ++ b) s.
  Proof.
    x_ind a; destruct n; simpl; conv; rewrite <- ?app_assoc; auto.
  Qed. 

  Lemma patch_del_app : forall a b i n,
    i + n <= length a ->
    patch_del a i n ++ b = patch_del (a ++ b) i n.
  Proof.
    x_ind a; simpl; auto. 
    destruct i, n; simpl; conv; auto. 
  Qed.

  Lemma patch_ins_app_right : forall a b s n,
    n <= length b ->
    a ++ patch_ins n b s = patch_ins (n + length a) (a ++ b) s.
  Proof. 
    x_ind a; conv; auto.
  Qed.

  Lemma patch_del_app_right : forall a b i n,
    i + n <= length b ->
    a ++ patch_del b i n = patch_del (a ++ b) (i + length a) n.
  Proof.
    x_ind a; simpl; auto; conv; auto. 
    f_equal. rewrite IHa; auto.
  Qed.
End ΔString.

Module StringLength <: StatelessDiffOp.
  Import ΔString.
  Definition A := string.
  Definition B := nat.
  Definition ΔA := Δstr.
  Definition ΔB := nat_change.
  Definition CA := stringc.
  Definition CB := natc.

  Definition f (s : string) : nat := length s.

  Definition Δf (Δs : CA.(ΔT)) : CB.(ΔT) :=
    match Δs with
    | noc => nat_add 0
    | ins i s => nat_add (length s)
    | del i n => nat_minus n
    end.

  Lemma inc_valid : forall (x : string) Δx, vc Δx x -> vc (Δf Δx) (f x).
  Proof.
    x_ind Δx; x_inv H; unfold f; auto.
  Qed.

  Hint Extern 4 => lia : core.
  Lemma inc_correct : forall x Δx (vcx : vc Δx x) vcy,
    f (patch Δx x vcx) = patch (Δf Δx) (f x) vcy.
  Proof.
    unfold f; x_ind x; x_inv vcx; simpl; dest_match; simpl; conv; auto.
  Qed.
End StringLength.

Module StringIsEmpty <: StatefulDiffOp.
  Import ΔString.

  Definition A := string.
  Definition B := bool.

  Definition CA := stringc.
  Definition CB := boolc.

  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).
  Definition ST := nat.
  Definition init (s : A) := length s.
  Definition inv (s : A) (st : ST) := st = length s.
  Definition vs (Δt : ΔA) t := match Δt with
      | ΔString.noc => True
      | ins i s => i <= t
      | del i n => i + n <= t 
      end.
  
  Definition Δst (Δx : ΔA) (st : ST) (hvs : vs Δx st) := match Δx with
      | ΔString.noc => st
      | ins i s => st + length s
      | del i n => st - n
      end.


  Definition f (x : A) := 
    match x with [] => true | _ => false end.
  

  Definition Δf (Δs : ΔA) (st : ST) (hvs : vs Δs st): ΔB :=
    match Δs with
    | noc => bool_noc
    | ins i s => match st with 
      | O => match s with | nil => bool_noc | _ => bool_neg end
      | _ => bool_noc end
    | del i n => match st with
      | O => bool_noc
      | _ => if lt_dec n st then bool_noc else bool_neg
      end
    end.

  

  Lemma del_lt_false : forall n x,
    n < length x -> f (patch_del x 0 n) = false.
  Proof. x_ind n; destruct x; auto; simpl in *; try apply IHn; lia. Qed.

  Lemma del_ge_true : forall n x,
    n >= length x -> f (patch_del x 0 n) = true.
  Proof. x_ind n; destruct x; auto; simpl in *; try apply IHn; lia. Qed.

  Hint Extern 4 => lia : core.
  Hint Extern 4 => discriminate : core.

  Lemma state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof. unfold inv, vs; intros; destruct Δx; x_inv H; auto. Qed.

  Lemma inv_init : forall x, inv x (init x).
  Proof. x_ind x. Qed. 
  Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof.
    unfold inv, vs; x_ind x; subst; x_inv vcx; simpl; auto.
    - conv; auto.
    - conv; auto.
    - dest_match; simpl; auto; conv; auto.
  Qed.


  Lemma inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.
  Proof. x_ind Δx. Qed.

  Lemma inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).
  Proof.
    unfold inv.
    x_ind Δx; auto; x_inv vcx; destruct x, i; simpl in *; dest_match; auto.
    - destruct s; auto.
    - apply del_lt_false; auto.
    - x_inj. apply del_ge_true; auto.
  Qed.


End StringIsEmpty.

Module StringToUpperCase <: StatelessDiffOp.
  Import ΔString.
  Definition A := string.
  Definition B := string.
  Definition CA := stringc.
  Definition CB := stringc.
  Definition ΔA := CA.(ΔT).
  Definition ΔB := CB.(ΔT).

  Definition is_lower (c : ascii) : bool :=
   (leb (ascii_of_nat 97) c) && (leb c (ascii_of_nat 122)).
    

  Definition to_upper (c : ascii) : ascii :=
    match (is_lower c) with
    | true => ascii_of_nat (nat_of_ascii c - 32)
    | false => c
    end.

  Definition f (s : string) : string := map to_upper s.

  Definition Δf (Δs : ΔA): ΔB :=
    match Δs with
    | ins i s => ins i (f s)
    | _ => Δs
    end.

  Lemma inc_valid : forall (x : A) Δx,
    Δx ↪ x -> (Δf Δx) ↪ (f x). 
  Proof.
    unfold f.
    x_ind Δx; x_inv H; constructor; rewrite ?length_map; auto.
  Qed. 

    Ltac correct_tac :=
    let H := fresh in
    repeat match goal with
    | |- ?c :: _ = ?c :: _ => f_equal 
    | [H : match ?x with | _ => _ end = _ |- _] => destruct x; auto
    | [H : ?g _ _ |- _<= _] => try (inversion H; simpl in *; lia)
    | [H : forall Δx, _ -> f _ = _ |- _ (?patch (ins ?n ?s) _) = ?patch _ _]
      => specialize H with (ins n s); simpl in *; apply H; constructor
    | [H : forall Δx, _ -> f _ = _ |- _ (?patch (del ?i ?n) _) = ?patch _ _]
      => specialize H with (del i n); simpl in *; apply H; constructor
    end.


  Lemma inc_correct : forall x Δx (vcx : vc Δx x) vcy,
    f (patch Δx x vcx) = patch (Δf Δx) (f x) vcy.
  Proof.
    unfold f.
    x_ind x; x_inv vcx; simpl in *; auto.
    - rewrite !patch_ins_empty_input; auto.
    - simpl. destruct n; rewrite ?patch_ins_empty_input; simpl; auto; unfold f in *. 
      + rewrite map_app; auto.
      + f_equal. specialize (IHx (ins n s)). 
        simpl in IHx. x_inv vcy; auto.
    - dest_match; x_inv vcy; auto.
      + specialize (IHx (del 0 n0)); simpl in IHx; rewrite IHx; auto.
      + simpl. f_equal. specialize (IHx (del n0 (S n1))); simpl in *. auto.
  Qed.
End StringToUpperCase.
Module StringToLowerCase <: StatelessDiffOp.
  Import ΔString.
  Definition A := string.
  Definition B := string.
  Definition CA := stringc.
  Definition CB := stringc.
  Definition ΔA := CA.(ΔT).
  Definition ΔB := CB.(ΔT).

  Definition is_upper (c : ascii) : bool :=
   (leb (ascii_of_nat 65) c) && (leb c (ascii_of_nat 90)).
  
  Definition to_lower (c : ascii) : ascii :=
    match (is_upper c) with
    | true => ascii_of_nat (nat_of_ascii c + 32)
    | false => c
    end.

  Definition f (s : string) : string := map to_lower s.

  Definition Δf (Δs : ΔA): ΔB :=
    match Δs with
    | ins i s => ins i (f s)
    | _ => Δs
    end.

  Lemma inc_valid : forall (x : A) Δx,
    Δx ↪ x -> (Δf Δx) ↪ (f x). 
  Proof.
    unfold f.
    x_ind Δx; x_inv H; constructor; rewrite ?length_map; auto.
  Qed. 

    Ltac correct_tac :=
    let H := fresh in
    repeat match goal with
    | |- ?c :: _ = ?c :: _ => f_equal 
    | [H : match ?x with | _ => _ end = _ |- _] => destruct x; auto
    | [H : ?g _ _ |- _<= _] => try (inversion H; simpl in *; lia)
    | [H : forall Δx, _ -> f _ = _ |- _ (?patch (ins ?n ?s) _) = ?patch _ _]
      => specialize H with (ins n s); simpl in *; apply H; constructor
    | [H : forall Δx, _ -> f _ = _ |- _ (?patch (del ?i ?n) _) = ?patch _ _]
      => specialize H with (del i n); simpl in *; apply H; constructor
    end.


  Lemma inc_correct : forall x Δx (vcx : vc Δx x) vcy,
    f (patch Δx x vcx) = patch (Δf Δx) (f x) vcy.
  Proof.
    unfold f.
    x_ind x; x_inv vcx; simpl in *; auto.
    - rewrite !patch_ins_empty_input; auto.
    - simpl. destruct n; rewrite ?patch_ins_empty_input; simpl; auto; unfold f in *. 
      + rewrite map_app; auto.
      + f_equal. specialize (IHx (ins n s)). 
        simpl in IHx. x_inv vcy; auto.
    - dest_match; x_inv vcy; auto.
      + specialize (IHx (del 0 n0)); simpl in IHx; rewrite IHx; auto.
      + simpl. f_equal. specialize (IHx (del n0 (S n1))); simpl in *. auto.
  Qed.
End StringToLowerCase.


Module StringConcat <: StatefulDiffOp.
  Import ΔString.
  Definition A := (string * string)%type.
  Definition B := string.
  Definition CA  := pairc stringc stringc.
  Definition CB := seqc stringc.
  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).

  Definition ST := nat.

  Definition patch_helper (Δx : Δstr) := match Δx with
    | noc => nat_add 0
    | ins i s => nat_add (length s)
    | del i n => nat_minus n
  end.

  Definition vc_helper (Δx : Δstr) (n : nat) := match Δx with
    | noc => True
    | ins i s => i <= n
    | del i k => i + k <= n
  end.

  Definition vs (Δt : ΔA) (t : nat) := match Δt with
      | pair_fst Δx => vc_helper Δx t
      | pair_both Δx _ => vc_helper Δx t
      | _ => True
    end.
  
  Definition Δst (Δx : ΔA) (st : ST) (hvs : vs Δx st) :=  
    match Δx with
    | pair_fst Δx => nat_patch (patch_helper Δx) st
    | pair_both Δx _ => nat_patch (patch_helper Δx) st
    | _ => st
    end.

  Definition f (s : A) := fst s ++ snd s.
  Definition shift (Δs : Δstr) n := match Δs with
    | noc => noc | ins i s => ins (i + n) s | del i k => del (i + n) k
  end.
  Definition Δf (Δs : ΔA) (st : ST) (hvs : vs Δs st): ΔB := match Δs with
    | pair_fst Δx => [Δx] | pair_snd Δx => [shift Δx st]
    | pair_both Δx Δy => [shift Δy st; Δx]
  end. 

  Definition init (t : A) := length (fst t).
  Definition inv x st := init x = st.

  Hint Extern 4 => lia : core.
  Hint Extern 4 => constructor : core.
  Export PeanoNat.Nat.

  Ltac conv := repeat match goal with
  | |- context [length (patch_ins _ _ _)] => rewrite patch_ins_length
  | |- context [length (patch_del _ _ _)] => rewrite patch_del_length
  | |- context [length (_ ++ _)] => rewrite length_app
  | |- context [patch_ins _ _ nil] => rewrite patch_ins_empty_inserted
  | |- context [_ ++ []] => rewrite app_nil_r
  | |- context [patch_del _ 0 0] => rewrite patch_del_empty
  | |- context [_ + S _] => rewrite add_succ_r
  end.

  Ltac y_inv := repeat match goal with
  | H : context[pair_vc] |- _ => x_inv H
  | H : context[str_vc] |- _ => x_inv H
  | H : context[seq_vc] |- _ => x_inv H
  end.


  Lemma state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof. 
    unfold inv, vs, vc_helper; intros x Δx st hvc hinv; dest_match; x_inv hvc; auto. 
    - unfold init; y_inv; auto.
    - unfold init; y_inv; auto.
  Qed.

  Lemma inv_init : forall x, inv x (init x).
  Proof. x_ind x. Qed. 
  Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof.
    unfold inv, vs; x_ind x; subst; x_inv vcx; simpl; auto; unfold init; simpl; conv; auto.
    x_inv H; x_inv H0; conv; auto.
  Qed.
  Hint Extern 4 => econstructor : core.
  Theorem inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.
  Proof.
    unfold inv, f, init.
    x_ind Δx; y_inv; repeat constructor; simpl in *; conv; auto.
    Unshelve.
    all: simpl; y_inv; constructor; conv; auto.
  Qed.

  Hint Resolve patch_ins_app patch_ins_app_right patch_del_app patch_del_app_right : core.

  Theorem inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).
  Proof.
    unfold f, inv, init.
    intros Δx x; revert Δx; x_ind x; y_inv; simpl in *; auto;
    rewrite ?patch_ins_app, ?patch_del_app; auto.
  Qed.

End StringConcat.


Module Type Char.
  Parameter c : ascii.
End Char.

Module ΔOption.
  Section ΔOptionImpl.
    Variable (T : Type) (c : change T).
    Notation ΔT := c.(ΔT).
    Inductive Δoption := 
    | o_noc : Δoption
    | to_some : T -> Δoption (* convert a none to a some value*)
    | as_some : ΔT -> Δoption (* apply a delta on a Some value *)
    | to_none : Δoption
    .
    Inductive option_vc : Δoption -> option T -> Prop :=
    | vc_noc t : option_vc o_noc t
    | vc_as_some t : option_vc (to_some t) None
    | vc_to_some t Δt : Δt ↪ t -> option_vc (as_some Δt) (Some t)
    | vc_to_none t : option_vc to_none t
    .

    Program Definition option_patch (Δt : Δoption) (t : option T) (vc : option_vc Δt t) := 
      match Δt with
      | o_noc => t
      | to_some k => Some k
      | as_some Δt => 
        match t with None => None | Some t => Some (patch Δt t _) end
      | to_none => None
      end.
    Next Obligation.
      x_inv vc; exact H1.
    Defined.


  Lemma option_patch_pir_dep : forall Δl1 Δl2 t1 t2 vc1 vc2,
    Δl1 = Δl2 -> t1 = t2 -> option_patch Δl1 t1 vc1 = option_patch Δl2 t2 vc2.
  Proof.
    intros * Heq1 Heq2; subst; x_inv vc1; x_inv vc2; auto; f_equal;
    erewrite patch_det; eauto.
    Unshelve. auto.
  Qed. 

  Hint Resolve option_patch_pir_dep : core.
  Lemma option_patch_pir : forall Δt t vc1 vc2, 
    option_patch Δt t vc1 = option_patch Δt t vc2.
  Proof. auto. Qed.
  
  Lemma option_patch_if : 
    forall T B (c : change T) (b : {B} + {~B}) l1 l2 t v1 v2 v3, 
      option_patch (if b then l1 else l2) t v1 =
      if b then option_patch l1 t v2 else option_patch l2 t v3.
  Proof.
    intros. dest_match; eauto.
  Qed.

  Lemma simplify_dep_match {A} (e : option A) (f : A -> Δoption) (g : Δoption) :
  forall (x : option T) hv hv1 hv2,
  option_patch (match e as x return (x = e -> Δoption) with
   | Some a => fun _ => f a
   | None => fun _ => g
   end hv) x hv1 = option_patch (match e with | Some a => f a | None => g end) x hv2.
  Proof. destruct e; intros; simpl; auto. Qed.


    Program Definition optionc : change (option T) := {|
      patch := option_patch
    ; vc := option_vc
    |}.
  End ΔOptionImpl.
  Arguments to_some {_ _}.
  Arguments as_some {_ _}.
  Arguments to_none {_ _}.
  Arguments o_noc {_ _}.
End ΔOption.
Module StringLastIndexOf(Import C : Char) <: StatefulDiffOp.
  Import ΔString ΔOption Difference.
  Definition A := string.
  Definition B := option nat.
  Definition CA := stringc.
  Definition CB := optionc nat natc.
  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).

  Definition ST := (A * B)%type.
  Definition vs (Δx : ΔA) (x : ST) : Prop := let (input, _) := x in vc Δx input.

  Definition f x := last_index_of x c.

  Hint Extern 4 => constructor : core.

  Program Definition Δst (Δx : ΔA) (x : ST) (hvs : vs Δx x) := 
      let (input, output) := x in
      let new_input := patch Δx (fst x) _ in
      match Δx, output with
      | noc, _ => x
      | ins i s, None => 
        match last_index_of s c with
        | None => (new_input, None)
        | Some k => (new_input, Some (k + i))
        end
      | ins i s, Some k =>
        if lt_dec k i
        then match last_index_of s c with
             | None => (new_input, Some k)
             | Some j => (new_input, Some (j + i))
             end 
        else (new_input, Some (k + length s))
      | del i n, None => (new_input, None)
      | del i n, Some k => 
        if lt_dec (i + n) k 
        then (new_input, Some (k - n))
        else if lt_dec k i 
        then (new_input, Some k)
        else (new_input, last_index_of new_input c)
      end.
    Next Obligation.
      unfold vs in hvs; simpl in hvs; dest_match; simpl; auto.
    Defined.


  Program Definition Δf (Δx : ΔA) (s : ST) (hvs : vs Δx s) : ΔB :=
    match Δx, (snd s) with 
    | ΔString.noc, _ => o_noc
    | ins i str, None => (* c is not found in the previous run*)
      match last_index_of str c with
      | None => o_noc
      | Some k => ΔOption.to_some (k + i)
      end
    | ins i str, Some k => (* k is the index of c in the last run*)
      if lt_dec k i (* insertion happens after k *)
      then match last_index_of str c with 
            | None => o_noc (* not found *)
            | Some j => @as_some _ natc (nat_add (j + i - k)) (* found a later occurrence *)
            end 
      else @as_some _ natc (nat_add (length str))
    | del i n, None => o_noc
    | del i n, Some k => 
      match lt_dec (i + n) k with 
      | left Hlt => @as_some _ natc (nat_minus n)
      | right Hr => 
      match lt_dec k i with 
      | left Hlt => o_noc
      | right Hr => 
      match last_index_of (patch Δx (fst s) _) c with
      | None => to_none 
      | Some j => @as_some _ natc (diff NatDiff k j)
      end end end
    end.
  Next Obligation.
    unfold vs in hvs; simpl in hvs; dest_match; simpl; auto.
  Defined.

  Definition init (x : A) : ST := (x, last_index_of x c).

  Definition inv (x : A) (s : ST) := s = init x.
  Lemma state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof.
    unfold inv, vs, init; intros * hvc hinv; dest_match; x_inj; auto.
  Qed.
  Lemma inv_init : forall x, inv x (init x).
  Proof. x_ind x. Qed.
  (* Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof. *)
    
  Ltac x_valid := simpl; try x_inj; try econstructor; simpl; eauto.

  Theorem inc_valid : forall x Δx st (H : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st H sti) ↪ f x.
  Proof.
    unfold f, inv, init.
    intros x [|i s|i n]; x_ind x; simpl in *; simpl; auto; try x_inj; dest_match; auto; rewrite EQ in *; eauto; x_valid.
  Qed.

      


  Hint Extern 4 => discriminate : core.
  Hint Resolve last_index_of_skipn_n firstn_not_in skipn_not_in : core.


  Ltac x_tac := repeat match goal with
  | H : ?i <= length ?x |- context[last_index_of (patch_ins ?i ?x _) _] => rewrite patch_ins_split; [.. | exact H]
  | H : last_index_of ?x _ = Some ?n, H' : ?n < ?i |- last_index_of (firstn ?i ?x) _ = _ =>
    apply last_index_of_firstn
  | |- ~ In _ (_ ++ _) => let H := fresh in intro H; apply in_app_iff in H; destruct H 
  | H1 : In _ (skipn ?i ?x), H2 : ?n < ?i, H3: last_index_of ?x ?c = Some ?n |- _ =>
    eapply last_index_of_skipn_n with (i:=i) in H3; auto
  | H1 : ~ In ?c ?x, H2 : In ?c (skipn ?i ?x) |- _ => eapply skipn_not_in in H1; eauto
  | H1 : last_index_of ?x ?c = None |- last_index_of (firstn ?i ?x) ?c = None =>
    rewrite last_index_of_not_find in *
  | H1 : last_index_of ?s ?c = None, H2 : In ?c ?s |- _ => 
    rewrite last_index_of_not_find in H1; auto
  | H1 : last_index_of ?s ?c = None, H2 : In ?c (skipn ?i ?s) |- _ => 
    rewrite last_index_of_not_find in H1; eapply skipn_not_in in H1
  | |- In _ (_ ++ _) => apply in_app_iff
  | H : last_index_of ?s ?c = Some _ |- In ?c ?s => 
    apply last_index_of_some_in in H; auto
  | |- Some _ = Some _ => f_equal
  | H : last_index_of ?x ?c = None, H2 : last_index_of (_ ++ skipn _ ?x) _ = _ |- _ = _ =>
    rewrite last_index_of_split in H2
  | H : last_index_of ?x ?c = Some ?n, H1 : ?n < ?i, H2 : last_index_of (_ ++ skipn ?i ?x) _ = _ |- _ = _ =>
    rewrite last_index_of_split in H2
  | |- context [length (firstn ?i ?x)] =>
    rewrite firstn_length_le; [..|lia]
  | H1 : last_index_of ?s ?c = Some _, H2 : last_index_of ?s ?c = Some _ |- _ =>
    rewrite H1 in H2; x_inj
  | |- context[shift_option] => unfold shift_option; dest_match
  | H : context[shift_option] |- _ => unfold shift_option in H; dest_match
  | H : last_index_of (skipn ?i ?x) ?c = Some ?n, H1 : ?i <= length ?x |- _ =>
    eapply skipn_last_index_of in H; rewrite ?H in *; clear H
  | H : ?i + ?n <= length ?x |- context[patch_del ?x ?i ?n] =>
    rewrite patch_del_split; [.. | lia]
  | H : last_index_of ?x ?c = Some ?n |- ~ In ?c (skipn ?i ?x) =>
    eapply last_index_of_skipn_n in H; [eassumption | lia]
  | H : last_index_of ?x ?c = None, H1: In ?c (firstn ?i ?x) |- _ =>
    eapply firstn_in in H1 
  | H1 : last_index_of ?x ?c = Some ?n0, H2 : last_index_of (skipn ?n1 ?x) ?c = None |- None = Some _ => apply last_index_of_not_find in H2; apply last_index_of_skipn_n_in with (i:=n1)in H1
  | H : In _ (_ ++ _) |- _ => apply in_app_iff in H; destruct H
  | H : Some _ = Some _ |- _ => x_inj
  | H1 : last_index_of ?x ?c = None, H2 : last_index_of ?s ?c = None |- 
    context[last_index_of _ _] => rewrite last_index_of_not_find 
  | H1 : last_index_of ?x ?c = Some ?n, H2 : last_index_of ?s ?c = None |- 
    last_index_of (_ ++ ?s ++ _) ?c = Some ?n => rewrite last_index_of_split
  | H : last_index_of ?x ?c = None |- context[last_index_of (firstn _ ?x ++ skipn _ ?x)] => rewrite last_index_of_not_find
  | H : Some _ = last_index_of _ _ |- _ => symmetry in H
  | H : None = last_index_of _ _ |- _ => symmetry in H
  end.

  Hint Extern 4 => x_tac : core.
     
  Hint Resolve last_index_of_skipn_n_in : core.
(* Lemma simplify_dep_match {A B} (e : option A) (f : A -> B) (g : B) hv :
  (match e as x return (x = e -> B) with
   | Some a => fun _ => f a
   | None => fun _ => g
   end hv) = match e with | Some a => f a | None => g end.
Proof. destruct e; reflexivity. Qed. *)

  Theorem inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).
    Proof.
      unfold inv, init, f.
      intros x [|i str|i n] [input output] Hvc Hinv.
      - simpl; auto.
      - simpl. dest_match.
        + erewrite option_patch_if with (T:=nat); [.. | eapply natc].
          Unshelve. 2: { x_inj; dest_match; eauto. rewrite <- H; eauto.  } 2: { x_inj; rewrite <- H; eauto. }  
          dest_match; x_inv Hvc.
          * dest_match; x_tac.
            ** rewrite last_index_of_split_r; x_tac; auto.
            ** rewrite last_index_of_split; x_tac; eauto. 
          * rewrite <- H. x_tac; eauto; rewrite last_index_of_split_r; eauto.
          * dest_match; try x_inj; simpl.
            ** x_tac. rewrite !last_index_of_split_r in *; x_tac; eauto.
            ** auto.            
        + erewrite simplify_dep_match.
          Unshelve. 2: { dest_match; eauto; x_inj; rewrite <- H; eauto. } 
          simpl; dest_match;  x_inv Hvc.
          * simpl. 
            x_tac; try rewrite last_index_of_split_r; eauto.
            rewrite last_index_of_split; eauto.
          * simpl.  x_tac; rewrite H.
            x_tac; eauto. 
      - simpl; dest_match; x_inv Hvc.
        + erewrite option_patch_pir.
          Unshelve. 
          2:{
            dest_match; x_inj; rewrite <- ?H; eauto; constructor; simpl; eauto.
          }
          dest_match; simpl; dest_match; eauto; try x_inj; x_tac.
          Unshelve. 4 : { eauto. }
          * rewrite last_index_of_split_r; eauto.
          * rewrite last_index_of_split, H; eauto.
          *  
          (* erewrite simplify_dep_match.
            
            
            Unshelve.
          2:{
            dest_match; x_inj; rewrite <- ?H; eauto; constructor; simpl; eauto.
          }
          simpl.  *)
          set (res := last_index_of (patch_del input i n) c); dest_match.
          dependent destruction res.
          ** erewrite option_patch_pir_dep with (Δl2:=@as_some _ natc
(if lt_dec n0 n3
then nat_add (n3 - n0)
else nat_minus (n0 - n3))); [.. | dest_match; auto | reflexivity].
           Unshelve. 2: { dest_match; x_inj; rewrite <- H; try constructor; simpl; eauto.  }
          simpl.
          dest_match; eauto. Unshelve. 3: {eauto. }
          *** x_inj. x_inj.  rewrite <- x; eauto.
          *** x_inj. x_inj. rewrite <- x; eauto.
        ** erewrite option_patch_pir_dep with (Δl2:=to_none); [.. | dest_match; auto | reflexivity]. Unshelve. 2: { constructor. }
          x_inj. simpl. eauto.
      + x_tac; rewrite H; eauto.
    Qed.


  Theorem inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof.
    unfold inv, init, f.
    intros x [|i str|i n] [input output] Hvc Hinv; simpl; dest_match; x_inj; f_equal; symmetry; x_inv Hvc;  eauto.
    - x_tac; rewrite last_index_of_split_r; eauto.
    - x_tac; rewrite last_index_of_split_r; x_tac; eauto; 
      rewrite last_index_of_split_r in *; x_tac; eauto.
    - x_tac; rewrite last_index_of_split_r; x_tac; eauto.
    - x_tac; rewrite last_index_of_split_r; eauto.
    - x_tac. rewrite last_index_of_split; eauto.
  Qed.

End StringLastIndexOf.

Module StringIndexOf(Import C : Char) <: StatefulDiffOp.
  Import ΔString ΔOption Difference.
  Definition A := string.
  Definition B := option nat.
  Definition CA := stringc.
  Definition CB := optionc nat natc.
  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT).

  Definition ST := (A * B)%type.
  Definition vs (Δx : ΔA) (x : ST) : Prop := let (input, _) := x in vc Δx input.

  Definition f x := index_of x c.

  Hint Extern 4 => constructor : core.

  Program Definition Δst (Δx : ΔA) (x : ST) (hvs : vs Δx x) :=
      let new_input := (fst x) ⊕ Δx in
      match Δx with
      | ΔString.noc => x
      | ins i s => match (snd x) with 
        | None => match index_of s c with 
                  | None => (new_input, None)
                  | Some j => (new_input, Some (i + j)) 
                  end
        | Some j => if lt_dec j i 
                    then (new_input, Some j)
                    else match index_of s c with
                    | None => (new_input, Some (j + length s))
                    | Some k => (new_input, Some (i + k))
                    end
        end
      | del i n => match (snd x) with
        | None => (new_input, None)
        | Some j => if lt_dec j i
                    then (new_input, Some j)
                    else if lt_dec (i + n) j
                    then (new_input, Some (j - n))
                    else (new_input, index_of new_input c)
        end
      end.
  Next Obligation.
    unfold vs in hvs. simpl in *. destruct x; eauto.
  Defined.

(* 
  Definition st_patch_ins (s s' : string) (i : nat) (res : option nat) := 
 *)

  Program Definition Δf (Δx : ΔA) (x : ST) (hvs : vs Δx x) : ΔB := 
    match Δx, (snd x) with
    | ΔString.noc, _ => o_noc
    | ins i s, None => (* c cannot be found in original string*)
      match index_of s c with
      | None => o_noc
      | Some n => ΔOption.to_some (n + i)
      end
    | ins i s, Some k =>
      if lt_dec k i
      then o_noc
      else match index_of s c with
           | None => @as_some _ natc (nat_add (length s))
           | Some n => @as_some _ natc (diff NatDiff k (i + n))
           end
    | del i n, None => o_noc
    | del i n, Some k =>
      if lt_dec k i 
      then o_noc
      else if lt_dec (i + n) k 
      then @as_some _ natc (nat_minus n)
      else match index_of (patch Δx (fst x) _) c with
      | None => ΔOption.to_none
      | Some j => @as_some _ natc (diff NatDiff k j)
      end
    end.
  Next Obligation.
    destruct x; simpl in *; constructor. x_inv hvs; auto.
  Defined.
  

  Definition init (x : A) : ST := (x, index_of x c).

  Definition inv (x : A) (s : ST) := s = init x.
  Lemma state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof.
    unfold inv, vs, init; intros * hvc hinv; dest_match; x_inj; auto.
  Qed.
  Lemma inv_init : forall x, inv x (init x).
  Proof. x_ind x. Qed.
  Ltac x_valid := simpl; try x_inj; try econstructor; simpl; eauto.

  Theorem inc_valid : forall x Δx st (H : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st H sti) ↪ f x.
  Proof.
    unfold f, inv, init.
    intros x [|i s|i n]; x_ind x; simpl in *; simpl; auto; try x_inj; dest_match; auto; rewrite EQ in *; eauto; x_valid.
  Qed.

  
  

  Ltac x_tac := repeat match goal with
  | H : ?i <= length ?x |- context[index_of (patch_ins ?i ?x _) _] => rewrite patch_ins_split; [.. | exact H]
  | H : index_of ?x ?c = Some ?n, H1 : ?n < ?i |- index_of (firstn ?i ?x ++ _) ?c = _ => rewrite index_of_split
  | H : index_of ?x ?c = Some ?n, H1 : ?n < ?i |- index_of (firstn ?i ?x) ?c = _ =>
    eapply index_of_firsti_left
  | H : index_of ?x ?c = Some ?n, H1 : ?n < ?i |- In ?c (firstn ?i ?x) =>
    eapply index_of_firsti_in
  | |- ~ In _ (_ ++ _) => let Hin := fresh in intros Hin; apply in_app_iff in Hin; destruct Hin 
  | H1 : index_of ?x ?c = None, H2 : In ?c (firstn _ ?x) |- _ =>
    eapply index_of_firstn_not_in in H1
  | H1 : In _ (_ ++ _) |- _ => apply in_app_iff in H1; destruct H1
  | H1 : index_of ?x ?c = None, H2 : In ?c ?x |- _ =>
    eapply index_of_not_in in H1
  | H1 : index_of ?x ?c = None, H2 : In ?c (skipn _ ?x) |- _ =>
    eapply index_of_skipn_not_in in H1
  | H1 : index_of ?x ?c = None, H2: index_of ?s ?c = Some _  |- index_of (firstn ?i ?x ++ _) _ = _ =>
    rewrite index_of_split_r
  | |- context[shift_option] => unfold shift_option; dest_match
  | H : context[shift_option] |- _ => unfold shift_option in H; dest_match
  | H : Some _ = Some _ |- _ => x_inj
  | |- Some _ = Some _  => f_equal
  | |- context [length (firstn ?i ?x)] =>
    rewrite firstn_length_le; [..|lia]
  (* | H1 : index_of ?x ?c = None, H2 : index_of (skipn _ ?x) ?c = Some _ |- _ =>
    eapply index_of_in in H2; eapply index_of_not_in in H1 
  | H1 : In ?c (skipn ?i ?x), H2 : ~ In ?c ?x |- _ =>
    apply skipn_in in H1; contradiction *)
  | H1 : index_of ?s ?c = Some _ |- In ?c ?s => apply index_of_in in H1
  | H1 : index_of ?s ?c = Some _, H2 : index_of (?s ++ _) _ = _ |- _ =>
    rewrite index_of_split in H2
  (* | H1 : index_of ?s ?c = None, H2 : index_of (?s ++ _) _ = Some _ |- _ =>
    rewrite index_of_split_r in H2 *)
  | H1 : ?x = Some ?m, H2 : ?x = Some ?n |- _ => rewrite H1 in H2; x_inj
  | H1 : index_of ?x ?c = Some ?n, H2 : index_of (skipn ?i ?x) ?c = None |- None = Some _ => eapply index_of_skipn_n_in with (i:=i) in H1
  | H : ?i + ?n <= length ?x |- context[patch_del ?x ?i ?n] =>
    rewrite patch_del_split; [.. | lia]
  | H : index_of (skipn ?i ?x) ?c = Some _, H1 : index_of ?x ?c = Some ?n |- _ => 
    erewrite skipn_index_of in H; [..|eassumption|lia]
  | H8 : index_of (skipn ?k ?x) ?c = Some _, H9 : index_of ?x ?c = None |- _ => 
    eapply index_of_skipn_not_in with (i:=k) in H9; eapply index_of_in in H8
  | H : Some _ = index_of _ _ |- _ => symmetry in H
  | H : None = index_of _ _ |- _ => symmetry in H

  end.

  Hint Extern 4 => x_tac : core.

  Hint Resolve firstn_not_in skipn_not_in firstn_in skipn_in index_of_skipn_n : core.


  Theorem inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).
    Proof.
      unfold inv, init, f.
      intros x [|i str|i n] [input output] Hvc Hinv.
      - simpl; auto.
      - simpl. dest_match.
        + erewrite option_patch_if with (T:=nat); [.. | eapply natc].
          Unshelve. 2: { x_inj; dest_match; eauto. }  2: { x_inj; rewrite <- H; eauto; dest_match; auto. constructor; simpl; auto. }  
          dest_match; x_inv Hvc.
          * dest_match; x_tac; rewrite ?H; eauto.
          * rewrite <- H. x_tac; eauto; rewrite index_of_split_r; eauto.
          * dest_match; try x_inj; simpl.
            ** x_tac. rewrite !index_of_split_r in *; x_tac; eauto.
            ** auto.            
        + erewrite simplify_dep_match.
          Unshelve. 2: { dest_match; eauto; x_inj; rewrite <- H; eauto. } 
          simpl; dest_match;  x_inv Hvc.
          * simpl. 
            x_tac; try rewrite index_of_split_r; eauto.
          * simpl. x_tac.   rewrite H, index_of_not_find.
            intro H3.
              rewrite !in_app_iff in H3.
              firstorder; eauto.
      - simpl; dest_match; x_inv Hvc.
        + erewrite option_patch_pir.
          Unshelve. 
          2:{
            dest_match; x_inj; rewrite <- ?H; eauto; constructor; simpl; eauto.
          }
          dest_match; simpl; dest_match; eauto; try x_inj; x_tac; eauto.
          * rewrite H. x_inv Hvc. eauto. 
          * x_inv Hvc . rewrite index_of_split_r; x_tac; eauto 2.
            erewrite skipn_index_of in EQ2; eauto.
          *  
          set (res := index_of (patch_del input i n) c); dest_match.
          dependent destruction res.
          ** erewrite option_patch_pir_dep with (Δl2:=@as_some _ natc
(if lt_dec n0 n3
then nat_add (n3 - n0)
else nat_minus (n0 - n3))); [.. | dest_match; auto | reflexivity].
           Unshelve. 2: { dest_match; x_inj; rewrite <- H; try constructor; simpl; eauto.  }
          simpl.
          dest_match; eauto. 
          *** x_inj. x_inj.  rewrite <- x; eauto.
          *** x_inj. x_inj. rewrite <- x; eauto.
        ** erewrite option_patch_pir_dep with (Δl2:=to_none); [.. | dest_match; auto | reflexivity]. Unshelve. 2: { constructor. }
          x_inj. simpl. eauto.
      + x_inv Hvc. x_tac; rewrite H, index_of_not_find.
            intro H3.
              rewrite !in_app_iff in H3.
              firstorder; eauto.
    Qed.

    
  Theorem inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof.
    unfold inv, init, f.
    intros x [|i str|i n] [input output] Hvc Hinv; simpl; dest_match; x_inj; f_equal; symmetry; x_inv Hvc;  eauto.

    - x_tac; rewrite index_of_split_r; eauto.
    - x_tac; rewrite index_of_split_r; x_tac; eauto; rewrite index_of_split_r in *; eauto. 
    - x_tac. rewrite index_of_not_find; eauto. 
    - x_tac; rewrite index_of_split_r; x_tac; eauto.
      eapply index_of_skipn_n_in with (i:=i+n) in H; eauto.
    - x_tac; rewrite index_of_split_r; x_tac; eauto. 
  Qed.

End StringIndexOf.