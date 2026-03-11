From AUTOINC Require Import EqDec Tactic.
From Stdlib Require Import Lia List.
Import ListNotations.
Set Implicit Arguments.

Declare Scope dict_scope.
Open Scope dict_scope.

Section ListDict.
    
  Variable K V : Type.
  Context `{EqK : EqDec K}.

  Implicit Type k : K.
  Implicit Type v : V.

  Inductive dict :=
  | dnil : dict
  | dcons : K -> V -> dict -> dict.

  Implicit Type d : dict.

  Fixpoint dict_keys d : list K :=
    match d with
    | dnil => []
    | dcons k v d => k :: (dict_keys d)
    end.

  Fixpoint dict_in k d : Prop := 
    match d with
    | dnil => False
    | dcons k' _ d => if eq_dec k k' then True else dict_in k d
    end.

  Inductive dict_in_dep : K -> dict -> Type :=
  | din_k d k v : dict_in_dep k (dcons k v d)
  | din_r d k k' v' : dict_in_dep k d -> dict_in_dep k (dcons k' v' d)
  .

  Fixpoint dict_get_dep {k d} (dep : dict_in_dep k d) : V :=
    match dep with
    | din_k d k v => v
    | din_r k' v' dep => dict_get_dep dep
    end.


  Lemma dict_in_keys : forall d k, dict_in k d <-> In k (dict_keys d).
  Proof. x_ind d; firstorder. subst. congruence. Qed.

  Lemma dict_in_dec : forall d k, {dict_in k d} + {~ dict_in k d}.
  Proof.
    induction d; intros; simpl; auto; dest_match; auto.
  Qed.

  Notation "k '∈' d" := (dict_in k d) (at level 30).

  Definition dict_no_dup d : Prop := NoDup (dict_keys d).
  Hint Extern 4 => congruence : core.
  Hint Extern 4 => constructor : core.

  Lemma dict_keys_no_dup : forall d, dict_no_dup d -> NoDup (dict_keys d).
  Proof.
    induction d; intros; simpl; auto.
  Qed.

  Lemma in_dcons :
    forall d k k0 v, k0 ∈ (dcons k v d) <-> k = k0 \/ k0 ∈ d.
  Proof.
    x_ind d; firstorder.
  Qed.
 
  Lemma nodup_dcons : forall d k v, dict_no_dup (dcons k v d) -> dict_no_dup d.
  Proof.
    unfold dict_no_dup. simpl.
    induction d; auto; intros; simpl in *; constructor; 
    inversion H; inversion H3; subst; auto.
  Qed.

  Hint Resolve in_dcons nodup_dcons : core.


  Fixpoint dict_add d k v : dict :=
    match d with
    | dnil => dcons k v dnil
    | dcons k' v' d' => if eq_dec k k'
                     then dcons k v d'
                     else dcons k' v' (dict_add d' k v)
    end.

  Lemma dict_add_in : forall (d : dict) k0 k v,
      k0 ∈ (dict_add d k v) <-> k = k0 \/ k0 ∈ d.
  Proof.
    x_ind d; split; simpl; dest_match; firstorder. 
  Qed.

  Lemma dict_add_no_dup : forall d k v, 
    dict_no_dup d -> dict_no_dup (dict_add d k v).
  Proof.
    unfold dict_no_dup.
    x_ind d; simpl. constructor; simpl; inversion H; subst.
    - rewrite <- dict_in_keys. rewrite dict_add_in. unfold "~". 
      intros H1; destruct H1; subst; firstorder. rewrite dict_in_keys in H0. 
      auto.
    - auto.
  Qed.

  Fixpoint dict_get d k : option V := 
    match d with
    | dnil => None
    | dcons k' v d => if eq_dec k k' then Some v else dict_get d k
    end.

  Lemma dict_get_some : forall d k v, dict_get d k = Some v -> dict_in k d.
  Proof.
    induction d; simpl; intros. auto. dest_match. auto. unfold dict_in. firstorder.
  Qed.

  Lemma dict_get_none : forall d k, dict_get d k = None <-> ~ dict_in k d.
  Proof.
    induction d; split; simpl; intros; unfold dict_in; simpl; auto; dest_match; firstorder.
  Qed.
  
  Fixpoint dict_add_with d k default (f : V -> V) :=
    match d with
    | dnil => dcons k default dnil
    | dcons k' v' d' => if eq_dec k k'
                       then dcons k (f v') d'
                       else dcons k' v' (dict_add_with d' k default f)
    end.

  Lemma dict_add_with_in : forall d k0 k v f,
    dict_in k0 (dict_add_with d k v f) <-> dict_in k0 (dict_add d k v).
  Proof.
    induction d.
    - tauto.
    - intros k0 k1 v0 f. simpl. destruct (eq_dec k1 k); subst; auto;
        split; intro H; apply in_dcons; apply in_dcons in H as [H|H]; auto.
      + apply IHd in H. auto.
      + apply <- IHd in H. eauto.
  Qed.

  (* Hint Extern 4 => rewrite dict_add_with_in in * : core.
  Hint Extern 4 => rewrite dict_add_with in * : core. *)
  (* Hint Extern 4 => rewrite dict_in_keys in * : core.  *)

  Lemma dict_add_with_no_dup : forall d k default f, 
    dict_no_dup d -> dict_no_dup (dict_add_with d k default f).
  Proof.
    unfold dict_no_dup.
    x_ind d; simpl. inversion H; subst. constructor; firstorder.
    rewrite <- dict_in_keys. unfold "~". intros. 
    rewrite dict_add_with_in in H0. rewrite dict_add_in in H0.  
    firstorder. rewrite dict_in_keys in *. auto.
  Qed.

  Lemma dict_add_with_get_some : forall d k n default f,
    dict_get d k = Some n ->
    dict_get (dict_add_with d k default f) k = Some (f n).
  Proof.
    x_ind d; intros; auto. 
    - x_inj; unfold dict_get; simpl; dest_eq_dec; auto.
    - simpl. dest_match; auto.
  Qed.

  Lemma dict_add_with_get_none : forall d k default f,
    dict_get d k = None ->
    dict_get (dict_add_with d k default f) k = Some default.
  Proof.
    x_ind d. simpl. dest_match; firstorder.
  Qed.

  Lemma dict_add_with_not_in : forall d k a default f,
    a <> k ->
    dict_get (dict_add_with d k default f) a = dict_get d a.
  Proof.
    x_ind d; simpl; dest_match; auto.
  Qed.

  Lemma dict_add_with_empty : forall d k default f, 
    dict_add_with d k default f = dnil -> False.
  Proof.
    intros. induction d; simpl in *; auto. dest_match; auto.
  Qed.

  Fixpoint dict_fold {T} d (f : K -> V -> T -> T) (t : T) : T := 
    match d with
    | dnil => t
    | dcons k v d => dict_fold d f (f k v t)
    end.


  Definition dj_dict (d1 d2 : dict) : Prop := forall k, (k ∈ d1 -> ~ k ∈ d2) /\ (k ∈ d2 -> ~ k ∈ d1).

End ListDict.
Arguments dnil {K V}.
