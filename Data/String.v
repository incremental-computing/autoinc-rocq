From Stdlib Require Import Ascii List Lia.
From AUTOINC Require Import Tactic List.
Import ListNotations.
Set Default Timeout 5.


Global Notation string := (list ascii).

Local Notation ws := " "%char. (* white space*)
Ltac dest_in c s := destruct (in_dec ascii_dec c s).


Hint Extern 4 => congruence : core.
Hint Extern 4 => constructor : core.


(* Facts about whitespace strings. 
Why not define whitespace string with a simple proposition: forall i \in l, i = " "?
Explanation: 
1. It is not as informative as defining it using inductive propositions like ws_str.
2. Using its negation is also inconvenient, especially in a constructive logic, in which we cannot freely convert ~∃x. ... to ∀x. ...
For example, it will be very difficult to prove trim_rh_nws if we define ws_str as a trivial proposition and use its negation.
*)
Section WSSTR.
  Inductive ws_str : string -> Prop :=
  | ws_str_nil : ws_str []
  | ws_str_cons : forall s a, ws_str s -> a = ws -> ws_str (a :: s).

  Lemma ws_app_intro : forall l1 l2, ws_str l1 -> ws_str l2 -> ws_str (l1 ++ l2).
  Proof.
    induction l1; simpl; intros; firstorder.
    constructor; inversion H; subst; auto.
  Qed.
  
  Lemma ws_str_tail : forall l a, ws_str (a :: l) -> ws_str l.
  Proof. intros. inversion H; subst. auto. Qed.

  Lemma ws_app_elim_l : forall l1 l2, ws_str (l1 ++ l2) -> ws_str l1.
  Proof. x_ind l1. inversion H; subst; eauto. Qed.
  
  Lemma ws_app_elim_r : forall l1 l2, ws_str (l1 ++ l2) -> ws_str l2.
  Proof. x_ind l1. inversion H; subst; eauto. Qed.

  Lemma ws_app_ws : forall l, ws_str l -> l ++ [ws] = ws :: l.
  Proof. x_ind l; inversion H; subst; auto. rewrite IHl; auto. Qed.

  Lemma ws_comm : forall l1 l2, ws_str l1 -> ws_str l2 -> l1 ++ l2 = l2 ++ l1.
  Proof. 
    x_ind l1. rewrite app_nil_r. auto. inversion H; subst.
    rewrite IHl1, app_comm_cons, <- ws_app_ws, <- app_assoc; auto.
  Qed.    

End WSSTR.

Hint Resolve ws_str_tail ws_app_elim_l ws_app_elim_r ws_app_intro : core.

(* Facts about non-whitespace strings. *)
Section NWSSTR.

  Inductive nws_str : string -> Prop :=
  | nws_str_1 : forall l a, a <> ws -> nws_str (a :: l)
  | nws_str_2 : forall l a, nws_str l -> nws_str (a :: l)
  .
 
  Lemma nws_app_elim : forall l1 l2, nws_str (l1 ++ l2) -> nws_str l1 \/ nws_str l2.
  Proof. x_ind l1. inversion H; subst; eauto; firstorder. Qed.

  Lemma nws_app_l : forall l1 l2, nws_str l1 -> nws_str (l1 ++ l2).
  Proof. x_ind l1; inversion H; subst; auto. Qed. 

  Lemma nws_app_r : forall l1 l2, nws_str l2 -> nws_str (l1 ++ l2).
  Proof. x_ind l1; inversion H; subst. Qed.

End NWSSTR.

Lemma ws_str_dec : forall s, ws_str s \/ nws_str s.
Proof. 
  x_ind s; destruct IHs; auto. destruct (ascii_dec a ws); subst; eauto.
Qed.

Hint Resolve nws_app_l nws_app_r : core.

Section TrimLeft.  
  (* trimLeft: remove left whitespaces of a string.  *)
  Fixpoint trim_left (s : string) : string :=
    match s with
    | a :: s => if ascii_dec a ws then trim_left s else a :: s
    | _ => nil
    end.

  Lemma trim_l_ws_str : forall l, ws_str l -> trim_left l = nil.
  Proof.
    induction l; simpl; intros; auto. inversion H; subst. dest_match; eauto.
  Qed.  


  Lemma trim_l_nws_app : forall l1 l2, nws_str l1 -> trim_left (l1 ++ l2) = (trim_left l1) ++ l2.
  Proof. x_ind l1; inversion H; subst; auto. Qed.

  Lemma trim_l_ws_app : forall l1 l2, ws_str l1 -> trim_left (l1 ++ l2) = trim_left l2.
  Proof. x_ind l1; inversion H; subst; eauto. Qed.

  (* If a string l's first element is not whitespace, then trim_left l = l. *)
  Lemma trim_l_ideom :  forall l, hd ws l <> ws -> trim_left l = l.
  Proof. x_ind l. Qed.

  (* If a string is l1 ++ l2, and the head of l2 is not a whitespace, then 
  trim_left (l1 ++ l2) = (trim_left l1) ++ l2
  *)
  Lemma trim_l_concat_nws : forall l1 l2, hd ws l2 <> ws -> trim_left (l1 ++ l2) = (trim_left l1) ++ l2.
  Proof. x_ind l1. apply trim_l_ideom. auto. Qed.

End TrimLeft.

Section TrimRight.
  (* trimRight: remove right whitespaces of a string.  *)

  (* The helper function for implementing trimRight, where
     - s : the currently processed string.
     - s1 : storing the whitespaces that are on the left of s.
     - s2 : storing the string that are on the left of s2,
            which must be either empty string or a string containing non-whitespaces
    In summary, trim_right_helper s s1 s2 = s2 ++ s1 ++ trim_right s
  *)
  Fixpoint trim_right_helper (s s1 s2 : string) : string :=
    match s with
    | ws :: s => trim_right_helper s (s1 ++ [ws]) s2
    | nws :: s => trim_right_helper s [] (s2 ++ s1 ++ [nws])
    | [] => s2
    end.

  Definition trim_right (s : string) := trim_right_helper s [] [].

  Lemma trim_rh_ws : forall s s1 s2, 
    ws_str s ->
    trim_right_helper s s1 s2 = s2.
  Proof.
    x_ind s; simpl; inversion H; subst; auto.
  Qed.

  Hint Resolve trim_rh_ws : core.

  Lemma trim_rh_nws : forall s s1 s2, 
    nws_str s ->
    trim_right_helper s s1 s2 = s2 ++ s1 ++ (trim_right_helper s [] []).
  Proof.
    x_ind s; inversion H; subst; eauto.
    all: pose proof (ws_str_dec s) as Hs; destruct Hs.
    all: try (rewrite !trim_rh_ws; auto; fail).
    all: try (rew_both IHs; [rew_both IHs | ..]; auto; simpl;
    repeat (rewrite <- app_assoc; f_equal); fail).
  Qed.

  Lemma trim_r_ws_str : forall l, ws_str l -> trim_right l = nil.
  Proof.
    unfold trim_right; intros; rewrite trim_rh_ws; auto.
  Qed.  


  Lemma trim_r_nws_app : forall l1 l2, nws_str l2 -> trim_right (l1 ++ l2) = l1 ++ (trim_right l2).
  Proof. 
    unfold trim_right. 
    x_ind l1; simpl; rewrite trim_rh_nws; auto; rewrite IHl1; auto.
  Qed.

  Corollary trim_r_nws_cons : forall l c, nws_str l -> trim_right (c :: l) = c :: (trim_right l).
  Proof. intros. replace (c :: l) with ([c] ++ l). apply trim_r_nws_app; auto. auto. Qed.

  Lemma trim_r_ws_app : forall l1 l2, ws_str l2 -> trim_right (l1 ++ l2) = trim_right l1.
  Proof. 
    unfold trim_right.
    x_ind l1; simpl.
    all: pose proof (ws_str_dec l1) as Hl1; destruct Hl1.
    all: try (rewrite trim_rh_ws; auto; symmetry; auto; fail).
    all: try (rew_both trim_rh_nws; auto; rewrite IHl1; auto; fail).
  Qed.

  Corollary trim_r_ws_cons : forall l c, ws_str l -> trim_right (c :: l) = trim_right [c].
  Proof. 
    intros. replace (c :: l) with ([c] ++ l). 
    rewrite trim_r_ws_app; simpl; auto. auto.
  Qed. 

  (* If a string l's first element is not whitespace, then trim_left l = l. *)
  Lemma trim_r_ideom_app :  forall l a, a <> ws -> trim_right (l ++ [a]) = l ++ [a].
  Proof. 
    unfold trim_right.
    x_ind l; simpl;
    rewrite trim_rh_nws; auto; rewrite IHl; auto.
  Qed.

  Lemma trim_r_ideom : forall c, c <> ws -> trim_right [c] = [c].
  Proof. unfold trim_right; simpl; intros; dest_match; auto. Qed.

End TrimRight.

Section StringTrim.
  (* trim *)
  Definition trim (s : string) : string := 
    trim_left (trim_right s).

End StringTrim.

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

  Lemma count_ws_app_r : forall s c, c <> " "%char -> count_ws (s ++ [c]) = count_ws s. 
  Proof. induction s; simpl; intros; dest_match; auto. Qed.

  Lemma only_ws_dec : forall s, only_ws s = true \/ only_ws s = false.
  Proof. x_ind s. Qed.

  Lemma only_ws_str_equiv_pos : forall s, only_ws s = true <-> ws_str s.
  Proof. split; x_ind s; inversion H; subst; auto. Qed. 

  Lemma only_ws_str_equiv_neg : forall s, only_ws s = false <-> nws_str s.
  Proof. split; x_ind s; inversion H; subst; auto. Qed.

End ONLYWS.



Definition shift_option (r : option nat) (x : nat) := 
  match r with
  | None => None
  | Some r => Some (x + r)
  end.

Infix "⊞" := shift_option (at level 30).

Section IndexOfChar.

  (* Index of a character *)
  Fixpoint index_of_helper (s : string) (c : ascii) i : option nat :=
    match s with
    | nil => None
    | x :: xs => if ascii_dec x c then Some i else index_of_helper xs c (S i)
    end.
  
  Definition index_of s c := index_of_helper s c 0.

  Hint Extern 4 => lia : core.

  Lemma index_of_helper_ge : forall s c i n,
    index_of_helper s c n = Some i ->
    i >= n.
  Proof. x_ind s; try x_inj; auto. eapply IHs in H. auto. Qed.

  Lemma index_of_helper_n : forall s c i m n,
    index_of_helper s c n = Some i ->
    index_of_helper s c m = Some (i - n + m).
  Proof.
    x_ind s; try x_inj; auto.
    eapply IHs with (m:=S m) in H as H1; auto.
    rewrite H1. f_equal.
    eapply index_of_helper_ge in H as H2.
    auto.
  Qed.
      

  Theorem index_of_find : forall s c i, 
    index_of s c = Some i -> 
    forall j, nth_error s j = Some c -> i <= j.
  Proof.
    unfold index_of.
    x_ind s; simpl in *.
    - x_inj. auto.
    - destruct j. 
      + simpl in *. x_inj; auto.
      + simpl in H0.
        eapply IHs with (i:=i-1) in H0; auto.
        erewrite index_of_helper_n; eauto.
  Qed.

  Lemma index_of_helper_none : forall s c i j,
    index_of_helper s c i = None ->
    index_of_helper s c j = None.
  Proof.
    x_ind s.
    eapply IHs in H; eauto.
  Qed.

  Theorem index_of_not_find_correct : forall s c, 
    index_of s c = None -> 
    forall d, List.In d s -> d <> c.
  Proof.
    unfold index_of.
    x_ind s; auto.
    destruct H0.
    - subst. auto.
    - apply IHs; auto. 
      eapply index_of_helper_none; eauto.
  Qed.

  Lemma index_of_empty : forall c k, index_of [] c <> Some k.
  Proof. unfold index_of; simpl; auto. Qed. 

  
  Lemma index_of_helper_extract : forall s c m n,
    m >= n -> index_of_helper s c m = (index_of_helper s c n) ⊞ (m - n).
  Proof.
    x_ind s; destruct H; auto; unfold shift_option; dest_match; eauto.
    - eapply index_of_helper_n with (m:= S (S m)) in EQ0 as H1; rewrite H1.
      assert (n1 >= S n). { apply index_of_helper_ge in EQ0; auto. }
      f_equal; lia.
    - eapply index_of_helper_none; eauto.
  Qed.

  Ltac x_solve := repeat match goal with
  | H : context[shift_option] |- _ => unfold shift_option in H; dest_match
  | |- context[shift_option] => unfold shift_option; dest_match
  | |- Some _ = Some _ => f_equal 
  | |- S _ = S _ => f_equal
  | H : index_of [] _ = Some _ |- _ => apply index_of_empty in H
  | _ : Some _ = Some _ |- _ => x_inj
  | |- context [index_of_helper _ _ (S _)] => rewrite index_of_helper_extract with (n:=0)
  (* | H : context [index_of_helper _ _ (S _)] |- _ => rewrite index_of_helper_extract with (n:=0) in H *)
  end.

  Hint Extern 4 => x_solve : core.

  Ltac gt_1 x := let H := fresh in assert (H : x >= 1); [eapply index_of_helper_ge; eauto|..] .

  Lemma index_of_split : forall s1 s2 c, 
    In c s1 -> index_of (s1 ++ s2) c = index_of s1 c.
  Proof.
    unfold index_of.
    x_ind s1; destruct H; subst; auto.
    eapply IHs1 with (s2:=s2) in H as H1.
    x_solve; eauto.
  Qed.

  Lemma index_of_split_r : forall s1 s2 c, 
    ~In c s1 -> index_of (s1 ++ s2) c = (index_of s2 c) ⊞ (length s1).
  Proof.
    unfold index_of.
    x_ind s1; unfold shift_option; dest_match; firstorder. 
    - x_solve; eauto.  
      + simpl; f_equal. 
        rewrite IHs1 in EQ1; dest_match; auto. 
      + eapply IHs1 with (s2:=s2) in H0; dest_match; eauto.
    - x_solve; eauto.
      rewrite IHs1 in EQ1; dest_match; eauto.
  Qed.

  Ltac index_subst H := rewrite index_of_helper_extract with (n:=0) in H; eauto.

  Lemma index_of_firsti_left : forall s c i n, 
    index_of s c = Some n -> n < i -> index_of (firstn i s) c = Some n.
  Proof.
    unfold index_of.
    x_ind s. eauto.
    - x_solve. destruct i; simpl; dest_match; eauto.
    - destruct i; simpl; dest_match; eauto.
      gt_1 n; x_solve; eauto.
      + simpl. erewrite IHs with (n:=n-1) in EQ1; eauto.
        index_subst H. 
      + erewrite IHs with (n:=n-1) in EQ1; index_subst H; eauto.
  Qed.

  Lemma index_of_firsti_in : forall s c i n,
    index_of s c = Some n -> n < i -> In c (firstn i s).
  Proof.
    unfold index_of.
    x_ind s; destruct i; simpl; eauto.
    right.
    gt_1 n.
    eapply IHs with (n:=n-1); eauto.
    index_subst H.
  Qed.

  Theorem index_of_not_find : forall s c, 
    index_of s c = None <-> ~ In c s.
  Proof.
    unfold index_of.
    x_ind s; split; intros; firstorder.
    intros H1; destruct H1; subst; auto.
    index_subst H; x_solve; firstorder.
  Qed.

  Lemma index_of_firstn_not_in : forall s c i,
    index_of s c = None -> ~ In c (firstn i s).
  Proof.
    unfold index_of.
    x_ind s; intros ?; destruct i; simpl in *; auto.
    destruct H0; subst; eauto.
    index_subst H; x_solve; firstorder.
  Qed.

  Lemma index_of_not_in : forall s c,
   index_of s c = None -> ~ In c s.
  Proof.
    unfold index_of.
    x_ind s; intros ?; destruct H0; auto. 
    index_subst H; x_solve; firstorder.
  Qed.

  Lemma index_of_skipn_not_in : forall s c i,
    index_of s c = None -> ~ In c (skipn i s).
  Proof.
    unfold index_of.
    x_ind s; intros ?; destruct i; simpl in *; auto.
    - destruct H0; subst; eauto. 
      index_subst H; x_solve; firstorder.
      pose proof index_of_not_in. 
      unfold index_of in H1. eapply H1 in EQ0; eauto.
    - index_subst H; x_solve; firstorder.
  Qed.

  Lemma index_of_in : forall s c n,
    index_of s c = Some n -> In c s.
  Proof.
    unfold index_of; x_ind s; right; index_subst H; firstorder.
    Unshelve. auto.
  Qed. 

  Lemma index_of_skipn_n : forall s c n i,
    index_of s c = Some n -> i <= n -> ~ In c (firstn i s).
  Proof.
    unfold index_of.
    x_ind s; try x_inj; destruct i; simpl; auto.
    intros Hn; destruct Hn; subst; auto.
    index_subst H; x_solve; auto. eapply IHs in EQ0; eauto.
  Qed.

  Lemma skipn_index_of : forall s n i c,
    index_of s c = Some n ->
    i <= n ->
    index_of (skipn i s) c = Some (n - i).
  Proof.
    unfold index_of.
    x_ind s; destruct i; simpl in *; dest_match; f_equal; eauto; index_subst H; x_solve; firstorder.
  Qed.

  Lemma index_of_skipn_n_in : forall s c n i,
    index_of s c = Some n -> i <= n -> In c (skipn i s).
  Proof.
    unfold index_of.
    x_ind s; simpl; try x_inj; destruct i; simpl in *; eauto; index_subst H; x_solve; auto.
    eapply IHs in EQ0; eauto.
    right.
    apply skipn_in in EQ0; eauto.
  Qed.

    
End IndexOfChar.

Section LastIndexOfChar.
  Fixpoint last_index_of_helper s c i res :=
  match s with
  | nil => res
  | x :: xs => 
    if ascii_dec x c 
    then last_index_of_helper xs c (S i) (Some i)
    else last_index_of_helper xs c (S i) res
  end.

  Definition last_index_of s c := last_index_of_helper s c 0 None.
  
  Hint Extern 4 => lia : core.

  Lemma last_index_of_helper_gt : forall c s i n j,
    last_index_of_helper s c n (Some j) = Some i -> i = j \/ i >= n.
  Proof.
    x_ind s. 
    - eapply IHs in H as ?. destruct H0; auto.
    - eapply IHs in H as ?; auto.
  Qed.

  Lemma last_index_of_not_in : forall s c n default,
    ~ In c s -> last_index_of_helper s c n default = default.
  Proof. x_ind s. firstorder. Qed. 

  Lemma last_index_of_in : forall s c n default_1 default_2,
    In c s -> last_index_of_helper s c n default_1 = last_index_of_helper s c n default_2.
  Proof. x_ind s. firstorder. Qed. 


  Lemma last_index_of_helper_ge : forall s c i n default,
    last_index_of_helper s c n default = Some i ->
    In c s -> i >= n.
  Proof.
    x_ind s; destruct H0.
    - dest_in c s.
      + eapply IHs in H; auto.
      + eapply  last_index_of_not_in with (n:= S n)(default:=Some n) in n0. 
        rewrite H in n0; auto. x_inj; auto.
    - eapply IHs in H as ?; auto.
    - auto.
    - eapply IHs in H; auto.
  Qed.

  Lemma last_index_of_helper_n : forall s c i m n default_1 default_2,
    last_index_of_helper s c n default_1 = Some i ->
    In c s ->
    last_index_of_helper s c m default_2 = Some (i - n + m).
  Proof.
    x_ind s; try x_inj; auto; destruct H0. 
    - dest_in c s.
      + eapply IHs with (m:= S m)(default_2:=Some m) in H as ?; eauto.
        rewrite H1.
        eapply last_index_of_helper_ge in H; auto.
      + erewrite last_index_of_not_in in *; try x_inj; eauto.
    - eapply IHs with (m:= S m)(default_2:=Some m) in H as ?; eauto.
      rewrite H1.
      eapply last_index_of_helper_ge in H; auto.
    - auto.
    - eapply IHs with (m:= S m)(default_2:=default_2) in H as ?; eauto.
      rewrite H1. 
      eapply last_index_of_helper_ge in H; auto.
  Qed.

  Hint Resolve nth_error_In : core.

  Theorem last_index_of_find : forall s c i, 
    last_index_of s c = Some i -> 
    forall j, nth_error s j = Some c -> j <= i.
  Proof.
    unfold last_index_of.
    x_ind s; simpl in *.
    - destruct j; auto;
      simpl in H0;
      assert (i >= 1).
      { eapply last_index_of_helper_ge; eauto. }
      eapply IHs with (i:= i - 1) in H0.
      auto.
      erewrite last_index_of_helper_n; eauto.
    - destruct j; simpl in *; auto.
         assert (i >= 1).
      { eapply last_index_of_helper_ge; eauto. }
      eapply IHs with (i:= i - 1) in H0.
      auto.
      erewrite last_index_of_helper_n; eauto.
  Qed.

  Lemma last_index_of_helper_some : forall s c i n,
    last_index_of_helper s c n (Some i) = None -> False.
  Proof. x_ind s. Qed.

  Hint Resolve last_index_of_helper_some : core.

  Lemma last_index_of_helper_none : forall s c i j,
    last_index_of_helper s c i None = None ->
    last_index_of_helper s c j None = None.
  Proof. x_ind s. eapply last_index_of_helper_some in H; auto. eauto. Qed. 

  Ltac x_dest_in := match goal with
  | H : ~ In ?c ?s, H' : last_index_of_helper ?s ?c _ _ = _ |- _ =>
    rewrite last_index_of_not_in in H'; auto
    end.

  Lemma last_index_of_is_in : forall s c i j, 
    last_index_of_helper s c j None = Some i -> In c s.
  Proof.
    unfold last_index_of.
    x_ind s; auto.
    right.
    dest_in c s. auto.
    x_dest_in.
  Qed.

  Theorem last_index_of_some_in : forall s c i, 
    last_index_of s c = Some i -> In c s.
  Proof.
    unfold last_index_of. intros.
    apply last_index_of_is_in in H; auto.
  Qed.

  Hint Extern 4 => congruence : core.

  Lemma last_index_of_helper_not_find : forall s c n, 
    last_index_of_helper s c n None = None <-> ~ In c s.
  Proof.
    x_ind s; split; intros Hn; firstorder.
    intros H; destruct H; auto; eapply last_index_of_helper_some in Hn; auto.
  Qed.

  Theorem last_index_of_not_find : forall s c, 
    last_index_of s c = None <-> ~ In c s.
  Proof.
    unfold last_index_of; intros; apply last_index_of_helper_not_find.
  Qed.

  Lemma last_index_of_empty : forall c, last_index_of [] c = None.
  Proof. unfold last_index_of; simpl; auto. Qed.
  

  Ltac x_solve := repeat match goal with
  | H : last_index_of_helper _ _ _ (Some _) = None |- _ => 
    eapply last_index_of_helper_some in H
  | H : last_index_of_helper ?s ?c _ None = Some _ |- In ?c ?s => 
    eapply last_index_of_is_in in H 
  | H : ?n >= 1, H' : ~ In _ (skipn (S (?n -1 + 0)) _) |- _ =>
    replace (S (n - 1 + 0)) with n in H'; [auto| lia]
  | H : ~ In ?c ?s |- last_index_of_helper ?s ?c _ ?d = ?d =>
    rewrite last_index_of_not_in
  | H : ~ In ?c ?s |- ~ In ?c (skipn ?n ?s) => apply skipn_not_in
  | H : ?n >= 1, H' : ~ In _ (skipn (S (?n -1 + 0)) _) |- _ =>
    replace (n - 1 + 0) with (n-1) in H'; [..| lia]
  | |- In _ (_ ++ _) => apply in_app_iff
  | H1 : last_index_of_helper ?s ?c _ None = None, H2 : In ?c ?s |- _ =>
    rewrite last_index_of_helper_not_find in H1
  | H : last_index_of [] _ = Some _ |- _ => rewrite last_index_of_empty in H; discriminate
  end.

  Hint Extern 4 => x_solve : core.



  Lemma last_index_of_exists : forall s c m default,
    In c s ->
    exists n, last_index_of_helper s c m default = Some n.
  Proof.
    x_ind s; destruct H;simpl in *; auto.
    dest_in c s; eauto.
    exists m. eauto. 
  Qed.

  Hint Resolve in_app_iff : core.

  Ltac gt_1 x := let H := fresh in assert (H : x >= 1); [eapply last_index_of_helper_ge; eauto|..] .


  Lemma last_index_of_split : forall s1 s2 c, 
    ~In c s2 -> last_index_of (s1 ++ s2) c = last_index_of s1 c.
  Proof.
    unfold last_index_of.
    x_ind s1; simpl.
    - eapply IHs1 in H as ?. dest_in c s1.
      + eapply last_index_of_exists with (m:=1)(default:= Some 0) in i as H2; 
        destruct H2 as [? ?].
        eapply last_index_of_exists with (m:=0)(default:= None) in i as H3; 
        destruct H3 as [? ?].
        rewrite H2 in *; rewrite H1 in *.
        eapply last_index_of_helper_n with (m:=0) (default_2:=None) in H1 as ?; auto.
        rewrite H2 in H3; x_inj.
        eapply last_index_of_helper_n with (m:=1) (default_2:=Some 0) in H0. 
        * gt_1 x.
          rewrite H0. auto.
        * apply in_app_iff; auto.
      + rewrite !last_index_of_not_in; auto.
        intros ?. eapply in_app_iff in H1. destruct H1; auto.
    - eapply IHs1 in H as ?. dest_in c s1.
      + assert (In c (s1 ++ s2)).
        { eapply in_app_iff; eauto. }
        eapply last_index_of_exists with (m:=0)(default:= None) in i as H2; 
        destruct H2 as [? ?].
        eapply last_index_of_exists with (m:=0)(default:= None) in H1 as H5; 
        destruct H5 as [? ?].
        rewrite H2 in *. rewrite H3 in *.
        eapply last_index_of_helper_n with (m:=1) (default_2:=None) in H2 as ?; auto.
        eapply last_index_of_helper_n with (m:=1) (default_2:=None) in H3 as ?; auto.
      + rewrite !last_index_of_not_in; auto.
        intros ?. eapply in_app_iff in H1. destruct H1; auto.
  Qed.


  Ltac x_subst a H := eapply last_index_of_helper_n with (m:=a)(default_2:=@None nat) in H as ?.

  Arguments None {A}.
  Lemma last_index_of_skipn : forall s c n,
    last_index_of s c = Some n -> ~ In c (skipn (S n) s).
  Proof.
    unfold last_index_of.
    x_ind s; simpl.
    - dest_in c s; auto.
      x_subst 0 H; auto.
      gt_1 n.
      eapply IHs in H0 as H2; auto.
    - x_subst 0 H; auto.
      eapply IHs in H0 as H2; auto.
      gt_1 n; auto.
  Qed.

  Hint Resolve skipn_not_in : core.
  Lemma last_index_of_skipn_n : forall s c n i,
    last_index_of s c = Some n -> i > n -> ~ In c (skipn i s).
  Proof.
    unfold last_index_of.
    x_ind s.
    - dest_in c s.
     + destruct i; simpl in *; firstorder.
       intros Hn. 
       x_subst 0 H; auto.
       gt_1 n.
       eapply IHs with (i:=i) in H1; auto.
     + x_dest_in; x_inj.
       destruct i; simpl; auto.
    - x_subst 0 H; auto.
      gt_1 n.
      destruct i; simpl in *; auto.
      eapply IHs in H1; eauto.
  Qed.

  Lemma last_index_of_skipn_n_in : forall s c n i,
    last_index_of s c = Some n -> ~ n < i -> In c (skipn i s).
  Proof.
    unfold last_index_of.
    x_ind s; destruct i; simpl in *; auto.
    - dest_in c s. 
      + gt_1 n. x_subst 1 H; auto.
        replace (n - 1 + 1) with n in H2; [.. | auto].
        x_subst 0 H; auto.
        eapply IHs in H3; eauto.
      + rewrite last_index_of_not_in in H; try x_inj; eauto.
        Unshelve. auto.
    - dest_in c s. 
      + gt_1 n. x_subst 1 H; auto.
        replace (n - 1 + 1) with n in H2; [.. | auto].
        x_subst 0 H; auto.
        eapply IHs in H3; eauto.
      + rewrite last_index_of_not_in in H; try x_inj; eauto.
        Unshelve. auto.
  Qed.


  Lemma last_index_of_firstn : forall s c i n, 
    last_index_of s c = Some n -> i > n -> last_index_of (firstn i s) c = Some n.
  Proof.
    unfold last_index_of.
    x_ind s; simpl in *.
    - destruct i; simpl in *; auto; dest_match.
      + clear EQ EQ0 e.
        dest_in c s.
        * eapply last_index_of_helper_n with (m:=0)(default_2:=None) in H as ?; auto.
          gt_1 n; auto.
          eapply IHs with (i:=i) in H1 as H3; auto.
          eapply last_index_of_helper_n with (m:=1)(default_2:=Some 0) in H3.
          rewrite H3. auto.
          eapply last_index_of_is_in in H3; auto.
        * rewrite last_index_of_not_in in H; auto. x_inj.
          apply last_index_of_not_in, firstn_not_in; auto.
      + auto.
    - destruct i; simpl in *; auto; dest_match.
      + clear EQ EQ0.
        dest_in c s.
        * eapply last_index_of_helper_n with (m:=0)(default_2:=None) in H as ?; auto.
        * rewrite last_index_of_not_in in H; auto. 
      + clear EQ EQ0.
        assert (In c s). eapply last_index_of_is_in; eauto.
        gt_1 n.
        eapply last_index_of_helper_n with (m:=0)(default_2:=None) in H as ?; auto.
        eapply IHs with (i:=i) in H3; auto.
        eapply last_index_of_helper_n with (m:=1) (default_2:=None) in H3 as ?; eauto.
        rewrite H4. auto.
  Qed.


  Lemma last_index_of_split_r : forall s1 s2 c, 
    In c s2 -> last_index_of (s1 ++ s2) c = last_index_of s2 c ⊞ length s1.
  Proof.
    unfold shift_option, last_index_of.
    x_ind s1.
    - erewrite last_index_of_helper_n with (n:=0)(default_1:=None)(i:=length s1 + n); auto.
      rewrite IHs1; auto; dest_match; try x_inj; auto.
    - erewrite last_index_of_helper_n with (n:=0)(default_1:=None)(i:=length s1 + n0); auto.
      rewrite IHs1; auto; dest_match; try x_inj; auto.
  Qed.

  Lemma skipn_last_index_of : forall s n i c,
    i <= length s ->
    last_index_of (skipn i s) c = Some n ->
    last_index_of s c = Some (n + i).
  Proof.
    unfold last_index_of.
    x_ind s.
    - assert (i = 0). auto. subst. simpl in *. rewrite H0; auto.
    - destruct i; simpl in *; dest_match; auto.
      + rewrite H0; auto.
      + eapply IHs in H0; auto.
        erewrite last_index_of_helper_n; eauto; auto.
    - destruct i; simpl in *; dest_match; auto.
      + rewrite H0; auto.
      + eapply IHs in H0; auto.
        erewrite last_index_of_helper_n; eauto; auto.
  Qed.


End LastIndexOfChar.
