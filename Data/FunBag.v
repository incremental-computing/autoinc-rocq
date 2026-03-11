From AUTOINC Require Import EqDec Tactic.
From Stdlib Require Import Classes.SetoidClass Compare_dec PeanoNat FunctionalExtensionality Lia RelationClasses.

(** What has been decided:

1. Bag should be specified as a finite map.

The reason is twofold:
- Database is not an infinite relation, some operation might be not well-defined using infinite map (e.g. https://github.com/tchajed/database-stream-processing-theory/blob/fb6ff4416108710448ccd87473c5513c1a1179ea/src/zset.lean)
- Finite map's equality is derivable from CIC, while normal function's equality is not. Using finite map can enable us keeps a axiom-free implementation so far.

Currently we use a trivial function to represent map for simplicity, in the future we will replace it with finite map.

2. relational algebra operators do not perform distinction (for leveraging stateless incremental operators).
*)

Declare Scope bag_scope.
Open Scope bag_scope.

Section Bag.

  Variable T : Type.
  Context `{EqT : EqDec T}.

  Definition bag := T -> nat.

  #[refine, global] Instance bag_Setoid : Setoid bag := {
    equiv b1 b2 := forall x, b1 x = b2 x
  }.
  Proof.
    constructor; auto.
    unfold Transitive. intros. rewrite H, H0. auto.
  Qed.

  
  Definition empty_bag : bag := fun x => 0.

  Definition singleton a : bag := fun x => if eq_dec a x then 1 else 0.

  Definition is_sup (b : bag) a := le_dec 0 (b a).

  Definition distinct b : bag := fun x => if is_sup b x then 1 else 0.

  Definition subseteq (b1 b2 : bag) : Type := forall x, b1 x <= b2 x.

End Bag.



Arguments empty_bag {T EqT}.
Arguments is_sup [T].
Arguments distinct [T].
Arguments singleton [T EqT].
Arguments subseteq [T].


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
  Proof. unfold subseteq. intros. auto. Qed.

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

  Definition select (b : bag T) := fun x => 
    if f x then b x else 0.

End BagSelection.

Arguments select [T].

Section BagUnionAll.
  Variable T : Type.
  Context `{EqT : EqDec T}.

  Definition union_all b1 b2 : bag T := fun x => (b1 x) + (b2 x).

  Lemma union_all_comm : forall b1 b2, 
    union_all b1 b2 = union_all b2 b1.
  Proof.
    intros. apply functional_extensionality; intros.
    unfold union_all. lia. 
  Qed.

  Lemma union_all_subseteq : forall b1 b2, b1 ⊆ union_all b1 b2.
  Proof. intros. unfold subseteq; unfold union_all; intros; lia. Qed.
    
End BagUnionAll.

Arguments union_all [T].
Notation "b1 ⊎ b2" := (union_all b1 b2) (at level 50) : bag_scope.

Section BagUnionMax.
  Variable T : Type.
  Context `{EqT : EqDec T}.
  Definition union_max b1 b2 : bag T := fun x => max (b1 x) (b2 x).

  Lemma union_max_comm : forall b1 b2, 
    union_max b1 b2 = union_max b2 b1.
  Proof.
    intros. apply functional_extensionality; intros.
    unfold union_max. lia. 
  Qed.

End BagUnionMax.

Arguments union_max [T].


Section BagUnionDistinct.
  Variable T : Type.
  Context `{EqT : EqDec T}.

  Definition union_dist b1 b2 : bag T := fun x => 
    if lt_dec 0 (b1 x) then 1 else if le_dec 0 (b2 x) then 1 else 0.

  Lemma union_dist_comm : forall b1 b2, 
    union_dist b1 b2 = union_dist b2 b1.
  Proof.
    intros. apply functional_extensionality; intros.
    unfold union_dist. dest_match; lia. 
  Qed.


End BagUnionDistinct.

Arguments union_dist [T].

Section BagIntersection.
  (* bag intersection *)
  Variable T : Type.
  Context `{EqT : EqDec T}.

  Definition intersect b1 b2 : bag T := fun x => min (b1 x) (b2 x).  


  Lemma intersect_comm : forall b1 b2, 
    intersect b1 b2 = intersect b2 b1.
  Proof.
    intros. apply functional_extensionality; intros.
    unfold intersect. lia. 
  Qed.

End BagIntersection.

Arguments intersect [T].

Section BagProduct.
  (* cartesian product *)
  Variable T1 T2 : Type.
  Context `{EqT1 : EqDec T1, EqT2 : EqDec T2}.
  Definition product (b1 : bag T1) (b2 : bag T2) : bag (T1 * T2) := 
      fun p : T1 * T2 => let '(x, y) := p in (b1 x) * (b2 y).
End BagProduct.

Arguments product [T1 T2].
Notation "b1 ⋅ b2" := (product b1 b2) (at level 40) : bag_scope.

Section BagDiff.
  Variable T : Type.
  Context `{EqT : EqDec T}.

  Definition diff (b1 b2 : bag T) : bag T := fun x => b1 x - b2 x.

End BagDiff.

Arguments diff [T].

Section TotalMap.

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


Section EquiJoinTotalMap.
  Variable T1 : Type. (* Type of row in left table *)
  Variable T2 : Type. (* Type of row in right table *)
  Variable K : Type. (* Type of the index *)
  Context `{EqDec T1, EqDec T2, EqDec K}.
  Variable c1 : T1 -> K.
  Variable c2 : T2 -> K.

  Variable b1 : bag T1.
  Variable b2 : bag T2.

  Variable eqb : K -> K -> bool.

  Definition ix_ty := total_map K (total_map T1 nat).
  Definition build_ix (b1 : bag T1) : ix_ty :=
    fun k => fun v => if eq_dec k (c1 v) then b1 v else 0.
  
  Definition match_ix (b2 : bag T2) (ix : ix_ty) : bag (T1 * T2) :=
    fun p => let '(t1, t2) := p in ix (c2 t2) t1 * b2 t2.

  Definition equi_join : bag (T1 * T2) := match_ix b2 (build_ix b1).
  
End EquiJoinTotalMap.
Arguments equi_join {T1 T2 K _}.
Arguments build_ix {T1 K _}.
Arguments match_ix {T1 T2 K}.






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
