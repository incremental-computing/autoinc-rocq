From AUTOINC Require Import EqDec Tactic ListMap.
From Stdlib Require Import Compare_dec PeanoNat 
   FunctionalExtensionality Lia RelationClasses ZArith List.
Import ListNotations.


Declare Scope bag_scope.
Open Scope bag_scope.

Open Scope Z_scope.

Section Bag.

  Variable T : Type.

  Context `{EqT : EqDec T}.

  Inductive bag_elem : Type :=
  | b_pos : T -> bag_elem
  | b_neg : T -> bag_elem.

  Definition bag := list bag_elem.
  
  Definition empty_bag : bag := [].

  Definition singleton a : bag := [a].

  Fixpoint support (b : bag) (a : T) : Z :=
    match b with
    | [] => 0
    | (b_pos t) :: b => 1 + (support b a)
    | (b_neg t) :: b => -1 + (support b a)
    end.  
  
  Definition subseteq (b1 b2 : bag) : Type := forall x, support b1 x <= support b2 x.

End Bag.

Arguments b_pos {T}.
Arguments b_neg {T}.
Arguments empty_bag {T}.
Arguments support {T}.
Arguments singleton {T}.
Arguments subseteq {T}.

Notation "{ }" := empty_bag (format "{ }") : bag_scope.

Notation "{ b }" := (singleton b) : bag_scope.

Notation " b1 ⊆ b2 " := (subseteq b1 b2) (at level 50) : bag_scope.

Section BagSubset.
  Variable T : Type.
  Context `{EqT : EqDec T}.

  Implicit Type x : bag T.
  (* TODO: use a partial order to describe .*)
  Lemma subseteq_trans : forall x y z, 
    x ⊆ y -> y ⊆ z -> x ⊆ z.
  Proof.
    unfold subseteq.
    intros. specialize (H0 x0). specialize (H x0). lia. 
  Qed. 

  Lemma subseteq_ref : forall x, subseteq x x.
  Proof. unfold subseteq. intros. lia. Qed.

End BagSubset.

(* Relational operators 
  - union (✓), 
  - difference (✓), 
  - select (✓), 
  - product (✓),
  - equi-join (✓),
  - projection (x), 
  - rename (x)
*)

Section BagSelection.
  Variable T : Type.
  Context `{EqT : EqDec T}.
  Variable f : T -> bool.

  Notation extract := (fun x => match x with b_pos x => x | b_neg x => x end).
  

  Definition select (b : bag T) : bag T := 
    filter (fun x => if f (extract x) then true else false) b.

End BagSelection.

Arguments select [T].

Section BagUnionAll.
  Variable T : Type.
  Context `{EqT : EqDec T}.

  Definition union_all b1 b2 : bag T := b1 ++ b2.

  Lemma positive_diag : forall (p : positive), (p ?= p)%positive = Eq.
  Proof.
    intros. induction p; simpl in *; auto. 
  Qed.
  Lemma support_union_d : forall b1 b2 a, 
    support (union_all b1 b2) a = (support b1 a) + (support b2 a).
  Proof.
    unfold union_all. induction b1; simpl; intros; auto; 
    dest_match; try rewrite IHb1 in *; try lia.
    all: symmetry in EQ. 
    all: assert ((p = xH)%positive \/ (p > xH)%positive). 
    all: try lia.
    all: destruct H; try rewrite H; 
    try (simpl; lia; fail);
    try (rewrite Z.pos_sub_lt; try lia; fail).
    all: apply Zplus_minus_eq in EQ; rewrite EQ; rewrite EQ0; simpl; subst.
    - rewrite EQ0 in EQ. auto.
    - simpl. rewrite Z.pos_sub_diag. auto.
    - rewrite Z.pos_sub_spec.  simpl. rewrite positive_diag. auto.
    - simpl. auto.
    - rewrite <- Z.pos_sub_opp. lia. 
    - rewrite Z.pos_sub_lt; try lia. 
      assert ((p = p0)%positive \/ (p < p0)%positive \/ (p > p0)%positive). lia.
      x_dest; subst.
      + rewrite Z.pos_sub_diag. rewrite Z.pos_sub_lt; lia.
      + rewrite Z.pos_sub_lt; try lia. rewrite Z.pos_sub_gt; try lia.
      + assert ((p0 = xH)%positive \/ (p0 > xH)%positive). try lia. destruct H1.
        * subst. simpl. rewrite Z.pos_sub_lt; lia.
        * rewrite Z.pos_sub_lt; try lia. rewrite Z.pos_sub_lt; try lia.
  Qed. 

  Lemma union_all_comm : forall b1 b2 a, 
    support (union_all b1 b2) a = support (union_all b2 b1) a.
  Proof.
    unfold union_all. intros. rewrite !support_union_d; lia. 
  Qed.

End BagUnionAll.

Arguments union_all [T].
Notation "b1 ⊎ b2" := (union_all b1 b2) (at level 50) : bag_scope.


Section BagProduct.
  (* cartesian product *)
  Variable T1 T2 : Type.
  Context `{EqT1 : EqDec T1, EqT2 : EqDec T2}.
  
  (* interesting *)
  Definition elem_prod (p1 : bag_elem T1) (p2 : bag_elem T2) : bag_elem (T1 * T2) := 
    match p1, p2 with 
    | b_pos p1, b_pos p2 => b_pos (p1, p2)
    | b_pos p1, b_neg p2 => b_neg (p1, p2)
    | b_neg p1, b_pos p2 => b_neg (p1, p2)
    | b_neg p1, b_neg p2 => b_neg (p1, p2)
    end.

  Fixpoint product (b1 : bag T1) (b2 : bag T2) : bag (T1 * T2) := 
    match b1 with
    | [] => []
    | hd :: tl => (map (fun x => elem_prod hd x) b2) ++ (product tl b2)
    end.

      
End BagProduct.

Arguments product [T1 T2].
Notation "b1 ⋅ b2" := (product b1 b2) (at level 40) : bag_scope.

(* Section BagDiff.
  Variable T : Type.
  Context `{EqT : EqDec T}.

  Definition diff (b1 b2 : bag T) : bag T := .

End BagDiff. *)

(* Arguments diff [T]. *)

(* Section TotalMap.

  Variable K V : Type.
  Context `{EK : EqDec K}.
  
  Definition total_map := K -> V.
  
  Implicit Type k : K.
  Implicit Type v : V.
  Implicit Type m : total_map.
  Implicit Type op : V -> V -> V.

  Definition t_empty v : total_map := fun _ => v.
  
  Definition t_update m k v := fun k' => if eq_dec k k' then v else m k'.

  Definition t_combine m1 m2 op := fun k => op (m1 k) (m2 k).

End TotalMap.

Arguments t_combine [K V].
*)

Section EquiJoin.
  Variable T1 : Type. (* Type of row in left table *)
  Variable T2 : Type. (* Type of row in right table *)
  Variable K : Type. (* Type of the index *)
  Context `{EqDec T1, EqDec T2, EqDec K}.
  Variable c1 : T1 -> K.
  Variable c2 : T2 -> K.

  Variable b1 : bag T1.
  Variable b2 : bag T2.

  Definition eqb k1 k2 := if eq_dec k1 k2 then true else false.
  

  Definition ix_ty := dict K (dict T1 Z).
  (* Definition build_ix (b1 : bag T1) (d : ix_ty) : ix_ty :=
    match b1 with
    | nil => dnil
    | hd :: tl => let key := c1 hd in 
                  if dict_in_dec d key then
                    let d' := dict_get d key in
                    sorry
                  else
                    
    if dict_in_dec 
    
    fun k => fun v => if eq_dec k (c1 v) then b1 v else 0.
  
  Definition match_ix (b2 : bag T2) (ix : ix_ty) : bag (T1 * T2) :=
    fun p => let '(t1, t2) := p in ix (c2 t2) t1 * b2 t2.

  Definition equi_join : bag (T1 * T2) := match_ix b2 (build_ix b1).
   *)
End EquiJoin.
(* Arguments equi_join {T1 T2 K _}.
Arguments build_ix {T1 K _}.
Arguments match_ix {T1 T2 K}. *)






(* Section BagEquiJoin.

  Variables T1 T2 K : Type.
  Context `{EqT1 : EqDec T1, EqT2 : EqDec T2, EqK : EqDec K}.
  

  Definition equi_join b1 b2 (k1 : T1 -> K) (k2 : T2 -> K) 
      (eqb : K -> K -> bool) : bag (T1 * T2) := 
    let ix1 : Map K (set T1) := Map.from (map (fun r => (k1 r, r)) b1) in
    (* let ix2 := Map.from (map (fun r => (k2 r, r)) b1) in *)
    flatMap (fun r2 =>
       map (fun r1 => (r1, r2)) (ix1 (k2 r2))
    ) b2


    select (fun p : T1 * T2 => eqb (k1 (fst p)) (k2 (snd p))) 
            b1).


    select (fun p : T1 * T2 => eqb (k1 (fst p)) (k2 (snd p))) 
               (b1 ⋅ b2).

End BagEquiJoin. *)
