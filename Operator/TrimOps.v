From AUTOINC Require Import Change String List StringChange SeqChange Operator Tactic.
From Stdlib Require Import Ascii List Lia.
Import ListNotations.

(*
Operators:

[ ] toUpperCase (hard to implement in Coq)
[ ] concat
[ ] trim

*)

Hint Extern 4 => discriminate : core.
Hint Extern 4 => repeat econstructor : core.
Hint Extern 4 => congruence : core.

Section ONLYWS.

  Fixpoint only_ws (s : string) : bool :=
    match s with
    | nil => true
    | c :: s => if ascii_dec c " " then only_ws s else false
    end.

  Fixpoint count_ws (s : string) : nat :=
      match s with
      | nil => 0
      | c :: s => if ascii_dec c " " then S (count_ws s) else 0
      end.
  Lemma only_ws_app : forall s1 s2, only_ws (s1 ++ s2) = andb (only_ws s1) (only_ws s2).
  Proof. induction s1; simpl; dest_match; auto. Qed.

  Lemma count_ws_app_false : forall s1 s2, only_ws s1 = false -> count_ws (s1 ++ s2) = count_ws s1.
  Proof. induction s1; simpl; intros; dest_match; simpl; auto. Qed.

  Lemma count_ws_app_true : forall s1 s2, only_ws s1 = true -> count_ws (s1 ++ s2) = count_ws s1 + count_ws s2.
  Proof. induction s1; simpl; intros; dest_match; simpl; auto. Qed.

  Lemma only_ws_dec : forall s, only_ws s = true \/ only_ws s = false.
  Proof. x_ind s. Qed.

  Lemma only_ws_str_equiv_pos : forall s, only_ws s = true <-> ws_str s.
  Proof. split; x_ind s; inversion H; subst; auto. Qed. 

  Lemma only_ws_str_equiv_neg : forall s, only_ws s = false <-> nws_str s.
  Proof. split; x_ind s; inversion H; subst; auto. Qed.

End ONLYWS.


Ltac x_only_ws_app := rewrite only_ws_app; simpl; unfold andb; dest_match; auto.
Ltac x_count_ws_app l := destruct (only_ws l) eqn:?;
    (rewrite count_ws_app_true + rewrite count_ws_app_false); simpl; auto.

Module TrimLeftOp <: StatefulDiffOp.
  Definition A := string.
  Definition B := string.
  Definition CA := stringc.
  Definition CB := seqc stringc.

  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT). 
  
  (* Notation ws := " "%char. *)

  Definition f := trim_left. (* original function *)

  (* the number of leftmost whitespaces and whether the trimmed is only whitespace *)
  Definition ST : Type := nat * bool. 

  Definition inv t (st : ST) := st = (count_ws t, only_ws t).

  Definition vs (Δt : ΔA) (st : ST) := True.

  Definition Δf (Δt : ΔA) (st : ST) (_ : vs Δt st) : ΔB :=
    let '(ws, all_ws) := st in
    match Δt with
    | str_noc => []
    | str_prepend " " => []
    | str_prepend c => (list_mul ws (str_prepend " ")) ++ [str_prepend c]
    | str_append " " => if all_ws then [] else [str_append " "]
    | str_append c => [str_append c]
    end. 

  Definition Δst (Δt : ΔA) (st : ST) (_ : vs Δt st) : ST := 
    let '(ws, all_ws) := st in
    match Δt with
    | str_noc => st
    | str_prepend " " => (S ws, all_ws)
    | str_prepend _ => (0, false)
    | str_append " " => if all_ws then (S ws, all_ws) else (ws, all_ws)
    | str_append _ => (ws, false)
    end. 

  Definition init (t : A) := (count_ws t, only_ws t).

  Lemma inv_init : forall x, inv x (init x). 
  Proof. 
    unfold init, inv. auto.
  Qed.

  Lemma state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof. trivial. Qed.

  Lemma seq_vc_string : forall k l, @seq_vc string stringc k l.
  Proof. 
    induction k; intros; unshelve econstructor; auto. 
  Qed.

  Lemma inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.
  Proof.
    intros. unfold vc. simpl. apply seq_vc_string. 
  Qed.

  Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof.
    unfold inv. unfold vs.
    intros [|?] [|?|?] [? ?] ? ?; simpl; auto 1;
    inversion sti; dest_match; auto; f_equal; f_equal;
    try x_only_ws_app; try (x_count_ws_app l; fail).
    rewrite count_ws_app_true; simpl; auto; lia.
  Qed.
  
  Lemma vc_prepend_n_ws : forall n s a, @seq_vc string stringc (list_mul n (str_prepend a)) s.
  Proof.
    induction n; simpl; intros; auto.
  Qed.

  Hint Extern 4 => match goal with
    | [|-context [seq_vc (?l1 ++ ?l2, _)]] =>
      eapply seq_vc_app
    | [|- context [seq_vc (list_mul _ (str_prepend _), _)]] =>
      eapply vc_prepend_n_ws      
    end : core.

  Hint Resolve ws_app_intro seq_vc_free str_change_free : core.

  Lemma trim_left_correct : forall l v,
    @seq_patch string stringc (list_mul (count_ws l) (str_prepend " ")) (f l) v = l.
  Proof.
    x_ind l.
    assert (list_mul (count_ws l) (str_prepend " ") ++ [str_prepend " "] = list_mul (S (count_ws l)) (str_prepend " ")).
    { apply list_mul_cons_tail. }
    erewrite seq_patch_pir_dep.
    (* It looks weird because Coq type inference is not smart enough to tell list str_change is equivalent to a seq_change.*)
    2: rewrite <- H. 
    2: reflexivity.
    2: eauto.
    erewrite seq_patch_app.
    simpl.
    f_equal.
    eapply IHl.
    Unshelve. all: eauto.
  Qed. 

  Ltac trim_l_tac :=
  let H := fresh "H" in
  repeat match goal with
  | [H : only_ws ?l = true |- _] => rewrite only_ws_str_equiv_pos in H
  | [H : only_ws ?l = false |- _] => rewrite only_ws_str_equiv_neg in H
  | [_ : ws_str ?l |- context[trim_left (?l ++ _)]] => rewrite trim_l_ws_app
  | [_ : nws_str ?l |- context[trim_left (?l ++ _)]] => rewrite trim_l_nws_app
  | [_ : ws_str ?l |- context[trim_left ?l]] => rewrite trim_l_ws_str
  end.
  
  Lemma trim_l_ws : ws_str [" "%char].
  Proof. firstorder. Qed.

  Hint Resolve trim_l_ws trim_l_concat_nws : core.

  Lemma inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).
  Proof.
    unfold inv, f.
    intros [|x] [|?|?] ? ? sti; try destruct (ascii_dec a " "); try destruct (ascii_dec x " "); x_inv sti; simpl in *; auto 1. 
    - erewrite seq_patch_pir_dep; dest_match; try contradiction. shelve. 
      all:auto. Unshelve. all:auto. Unshelve. all:auto.
    - erewrite seq_patch_pir_dep; dest_match; try contradiction. shelve. 
      all:auto. Unshelve. all:auto.
    - erewrite seq_patch_pir_dep; dest_match; try contradiction. shelve. 
      all:auto. Unshelve. all:auto.
      (* The following ugly proof is because of dependent types in vc *)
      assert (str_prepend " "
      :: list_mul (count_ws l) (str_prepend " ") ++
         [str_prepend a] = list_mul (count_ws l) (str_prepend " ") ++
         [str_prepend " "] ++ [str_prepend a]).
      { rewrite app_assoc, app_comm_cons, list_mul_cons_tail. f_equal. }
      erewrite seq_patch_pir_dep.
      2: erewrite H0; reflexivity.
      erewrite seq_patch_app. 
      simpl. repeat f_equal.
      rewrite trim_left_correct; auto. auto.
      Unshelve. all: eauto.
    - erewrite seq_patch_pir_dep; dest_match; try contradiction. shelve.
      all: eauto. Unshelve. eauto. simpl. auto.
    - pose proof (only_ws_dec l). 
      (* Why the proof is in this style? Because dependent type in vc does not allow destruct the only_ws condition in the ite expression, even after seq_patch_pir_dep.  *)
      destruct H0.
      + erewrite seq_patch_pir_dep with (Δl2:=[])(t2:=trim_left l); eauto 1; simpl.
        trim_l_tac; eauto.  
        dest_match; auto.
      + erewrite seq_patch_pir_dep. 
        2: { rewrite H0. eauto. } (* Again, because Coq cannot figure out a list of changes is a seq_change, so we have to first select the second goal to helper the type checker. *)
        2: eauto.
        trim_l_tac; eauto.
    - erewrite seq_patch_pir_dep; dest_match; try contradiction. shelve.
      all: eauto. Unshelve. all: eauto.
    - erewrite seq_patch_pir_dep; dest_match; try contradiction. shelve.
      all: eauto. Unshelve. all: eauto.
    - erewrite seq_patch_pir_dep; dest_match; try contradiction. shelve.
      all: eauto. Unshelve. all: eauto.
  Qed.
      
End TrimLeftOp.        

(* Lemma seq_patch_if : 
  forall T B (c : change T) (b : {B} + {~B}) l1 l2 t v1 v2 v3, 
    seq_patch c (if b then l1 else l2) t v1 =
    if b then seq_patch c l1 t v2 else seq_patch c l2 t v3.
Proof. intros; dest_match; auto. Qed.

Lemma seq_patch_if_t : 
  forall T B (c : change T) (b : {B} + {~B}) Δx t1 t2 v1 v2 v3, 
    seq_patch c Δx (if b then t1 else t2) v1 =
    if b then seq_patch c Δx t1 v2 else seq_patch c Δx t2 v3.
Proof. intros; dest_match; auto. Qed. *)

Module TrimRightOp <: StatefulDiffOp.
  Definition A := string.
  Definition B := string.
  Definition CA := stringc.
  Definition CB := seqc stringc.

  Notation ΔA := CA.(ΔT).
  Notation ΔB := CB.(ΔT). 
  
  (* Notation ws := " "%char. *)

  Definition f := trim_right. (* original function *)

  (* the number of rightmost whitespaces and whether the trimmed is only whitespace *)
  Definition ST : Type := nat * bool. 
  
  Fixpoint init (s : string) : nat * bool :=
    match s with
    | nil => (0, true)
    | c :: tl => let (ws, all_ws) := init tl in
      if all_ws 
      then (if ascii_dec c " " then (S ws, true) else (ws, false))
      else (ws, false)
    end.

  Definition inv t (st : ST) := st = init t.

  Definition vs (Δt : ΔA) (st : ST) := True.

  Definition Δst (Δt : ΔA) (st : ST) (_ : vs Δt st) : ST := 
    let '(ws, all_ws) := st in
    match Δt with
    | str_noc => st
    | str_prepend c => 
      if ascii_dec c " " then 
        if all_ws then (S ws, all_ws) else (ws, all_ws)
      else 
        (ws, false)
    | str_append c => if ascii_dec c " " then (S ws, all_ws) else (0, false)
    end. 

  Definition Δf (Δt : ΔA) (st : ST) (_ : vs Δt st) : ΔB :=
    let '(ws, all_ws) := st in
    match Δt with
    | str_noc => []
    | str_prepend c  => 
      if ascii_dec c " "%char then
        if all_ws then [] else [str_prepend " "]
      else
        [str_prepend c]
    | str_append c =>
      if ascii_dec c " "%char then
        []
      else 
        (list_mul ws (str_append " ")) ++ [str_append c]
    end. 

  Lemma inv_init : forall x, inv x (init x). 
  Proof. 
    unfold init, inv. auto.
  Qed.

  Lemma state_valid : forall x Δx st,
    Δx ↪ x -> inv x st -> vs Δx st.
  Proof. trivial. Qed.

  Lemma seq_vc_string : forall k l, @seq_vc string stringc k l.
  Proof. 
    induction k; intros; unshelve econstructor; auto. 
  Qed.

  Lemma inc_valid : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st) ,
    Δf Δx st (state_valid x Δx st vcx sti) ↪ f x.
  Proof.
    intros. unfold vc. simpl. apply seq_vc_string. 
  Qed.
    
  Hint Extern 4 => discriminate : core.

  Lemma init_true_length : forall l n, init l = (n, true) -> length l = n.
  Proof. 
    induction l; simpl; intros; try x_inj; auto;
    dest_match; x_inj; eauto.
  Qed.

  Lemma init_true_all_ws : forall l n, (n, true) = init l -> ws_str l.
  Proof.
    x_ind l; simpl. constructor; auto. eapply IHl. eauto. 
  Qed. 

  Lemma init_true_append_wp : forall l n, init l = (n, true) -> 
    init (l ++ [" "%char]) = (n + 1, true).
  Proof.  
    x_ind l; eauto; x_inj; auto; specialize (IHl n0); 
    firstorder; x_inj; auto.
  Qed.

  Lemma init_false_append_wp : forall l n, init l = (n, false) -> 
    init (l ++ [" "%char]) = (n + 1, false).
  Proof.
    induction l; simpl; intros; auto.
    dest_match; auto.
    all: try apply init_true_length in EQ, EQ1.
    - rewrite length_app in EQ1; simpl in *; subst. x_inj. auto.
    - apply init_true_append_wp in EQ. rewrite EQ in EQ1. x_inj. auto.
    - firstorder.
    - firstorder.
  Qed.

  Lemma init_false_nws : forall l n, (n, false) = init l -> nws_str l.
  Proof.
    x_ind l; simpl. eapply nws_str_2. eauto. 
  Qed. 
  Hint Extern 4 => congruence : core.

  Lemma init_append_nwp : forall l a0, a0 <> " "%char -> init (l ++ [a0]) = (0, false).
  Proof. x_ind l; eauto; specialize (IHl a0); firstorder. Qed.
  
  Ltac simp_init_wp := 
    match goal with
    | [H : init (?k ++ [" "%char]) = _ |- _] => erewrite init_true_append_wp in H
    | [_ : ?a <>" "%char, H : init (?l ++ [?a]) = _ |- _ ] =>
      erewrite init_append_nwp in H
    end; try x_inj; eauto.

  Hint Resolve init_true_length : core.
  Hint Extern 4 => lia : core.

  Lemma inv_step : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st),
    inv (x ⊕ Δx ~ vcx) (Δst Δx st (state_valid x Δx st vcx sti)).
  Proof.
    unfold inv. unfold vs.
    simpl.    
    intros [|?] [|?|?] [? ?] ? ?; auto; simpl in *. 
    - x_inj. dest_match; try congruence.
    - x_inj. dest_match; try congruence.
    - dest_match; try congruence.
    - dest_match; x_inj; f_equal; try congruence.
      all: try (apply init_false_append_wp in EQ; rewrite EQ in EQ1; try x_inj; auto; fail).
      all: try (simp_init_wp; eauto 1; fail).
  Qed.

  Hint Extern 4 => repeat econstructor : core.
  Hint Extern 4 => congruence : core.

  Hint Resolve ws_app_intro init_true_all_ws init_false_nws : core.

  Lemma trim_right_fold : forall x, trim_right_helper x [] [] = trim_right x.
  Proof. auto. Qed.

  Ltac inv_conv := 
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    match goal with
    | [H1 : init ?k = (_, true) |- _ ] => symmetry in H1; apply init_true_all_ws in H1 as H2
    | [H1 : init ?k = (_, false) |- _ ] => symmetry in H1; apply init_false_nws in H1 as H2
    end.

  Lemma all_append_list_mul : forall n, all_append_seq (list_mul n (str_append " "%char)).
  Proof. x_ind n. Qed.

  Hint Resolve all_append_list_mul : core.
  
  Lemma trim_right_correct : forall l b n v,
    (n, b) = init l ->
    @seq_patch string stringc (list_mul n (str_append " ")) (trim_right_helper l [] []) v = l.
  Proof.
    induction l; intros.
    - simpl in *. x_inj; auto.
    - simpl in *. dest_match; simpl; x_inj; inv_conv; try congruence.
      all: try (rewrite trim_rh_ws in IHl; auto 1;
          erewrite seq_patch_pir_dep; [
            .. | eauto | rewrite trim_rh_ws; eauto
          ];
          erewrite str_append_seq; auto 1;   
          simpl; f_equal; eauto; fail).
      all: try (rewrite trim_rh_ws in IHl; auto 1;
          erewrite seq_patch_pir_dep; [
            .. |
            erewrite <- list_mul_cons_tail; eauto |
            rewrite trim_rh_ws; eauto
          ]; 
          simpl; erewrite seq_patch_app;
          simpl; erewrite IHl, ws_app_ws; eauto; fail).
      all: try (erewrite seq_patch_pir_dep; 
          [.. | reflexivity | erewrite trim_rh_nws; eauto 1];
          erewrite str_append_seq; auto 1;
          simpl; f_equal;
          remember (trim_right_helper l [] []) as l1; 
          symmetry;
          erewrite <- IHl; eauto 1;
          erewrite str_append_seq; eauto 1; fail).
    Unshelve. all: auto.
  Qed.

  Lemma inc_correct : forall x Δx st (vcx : Δx ↪ x) (sti : inv x st), 
    f (x ⊕ Δx ~ vcx) = f x ⊕ Δf Δx st (state_valid x Δx st vcx sti) ~ (inc_valid x Δx st vcx sti).
  Proof.
    unfold inv, f, trim_right, ST.
    intros x [|?|?] [? ?] ? sti.
    all: simpl in *; auto; dest_match; erewrite seq_patch_if; dest_match; simpl; eauto 1.
    all: try (apply init_true_all_ws in sti; rewrite !trim_rh_ws; auto; fail).
    all: try (eapply init_false_nws in sti; rewrite trim_rh_nws; auto; fail).
    - destruct b.
      + apply init_true_all_ws in sti. 
        rewrite !trim_rh_ws; auto.
      + apply init_false_nws in sti.
        rewrite !trim_right_fold.
        rewrite trim_r_ws_app; auto.
    - rewrite trim_right_fold; auto.
      erewrite seq_patch_app. simpl. f_equal.
      erewrite trim_right_correct; eauto.
      Unshelve. all: eauto.
      rewrite trim_r_ideom_app; easy.
  Qed.
       
End TrimRightOp.        
        