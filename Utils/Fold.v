(* Induction principle for fold_left *)
From Stdlib Require Import List.
Import ListNotations.


Lemma fold_left_ind : forall T1 T2 (f : T1 -> T2 -> T1) 
  (P : T1 -> Prop) init,
  (forall (x:list T2), x = [] -> P (fold_left f x init)) ->
  (forall x t, P t -> P (f t x)) ->
  forall l, P (fold_left f l init).
Proof.
  intros.
  generalize dependent H0.
  generalize dependent init.
  induction l; simpl; intros; auto; simpl.
  specialize (H []). simpl in H. auto.
  apply IHl; auto. intros. subst. simpl. apply H0.
  specialize (H []). simpl in H. auto.
Qed.