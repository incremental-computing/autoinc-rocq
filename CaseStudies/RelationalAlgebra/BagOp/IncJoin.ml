
open Bag
open Pair

type ('k, 'v) dict =
| Dnil
| Dcons of 'k * 'v * ('k, 'v) dict

(** val dict_add_with :
    'a1 eqDec -> ('a1, 'a2) dict -> 'a1 -> 'a2 -> ('a2 -> 'a2) -> ('a1, 'a2)
    dict **)

let rec dict_add_with eqK d k default f0 =
  match d with
  | Dnil -> Dcons (k, default, Dnil)
  | Dcons (k', v', d') ->
    (match eqK k k' with
     | true -> Dcons (k, (f0 v'), d')
     | false -> Dcons (k', v', (dict_add_with eqK d' k default f0)))

type 't bag = 't list

(** val list_del : 'a1 eqDec -> 'a1 list -> 'a1 -> 'a1 list **)


(** val product : 'a1 bag -> 'a2 bag -> ('a1, 'a2) prod bag **)

let rec product b1 b2 =
  match b1 with
  | Nil -> Nil
  | Cons (hd, tl) -> app (map (fun x -> (hd, x)) b2) (product tl b2)

module EquiJoin =
 struct
  type ('k, 't) join_ix = ('k, 't bag) dict

  (** val ix_diff_elem :
      'a1 eqDec -> 'a2 eqDec -> ('a2 -> 'a1) -> ('a1, 'a2) join_ix -> 'a2 ->
      ('a1, 'a2) join_ix **)

  let rec ix_diff_elem eqK eqT c d t =
    match d with
    | Dnil -> Dnil
    | Dcons (k, v, d0) ->
      (match eqK k (c t) with
       | true -> Dcons (k, (list_del eqT v t), d0)
       | false -> Dcons (k, v, (ix_diff_elem eqK eqT c d0 t)))

  (** val ix_diff_bag :
      'a1 eqDec -> 'a2 eqDec -> ('a2 -> 'a1) -> ('a1, 'a2) join_ix -> 'a2 bag
      -> ('a1, 'a2) join_ix **)

  let ix_diff_bag eqK eqT c d b =
    fold_left (ix_diff_elem eqK eqT c) b d

  (** val update_ix :
      'a2 eqDec -> ('a1 -> 'a2) -> ('a2, 'a1) join_ix -> 'a1 -> ('a2, 'a1)
      join_ix **)

  let update_ix eqK c d a =
    dict_add_with eqK d (c a) (Cons (a, Nil)) (fun x -> Cons (a, x))

  (** val ix_get : 'a2 eqDec -> ('a2, 'a1) join_ix -> 'a2 -> 'a1 bag **)

  let rec ix_get eqK d k =
    match d with
    | Dnil -> Nil
    | Dcons (k', v, d0) ->
      (match eqK k k' with
       | true -> v
       | false -> ix_get eqK d0 k)

  (** val build_ix_helper :
      'a2 eqDec -> ('a1 -> 'a2) -> 'a1 bag -> ('a2, 'a1) join_ix -> ('a2,
      'a1) join_ix **)

  let build_ix_helper eqK c b init0 =
    fold_left (update_ix eqK c) b init0

  (** val build_ix :
      'a2 eqDec -> ('a1 -> 'a2) -> 'a1 bag -> ('a2, 'a1) join_ix **)

  let build_ix eqK c b =
    build_ix_helper eqK c b Dnil

  (** val match_ix :
      'a3 eqDec -> ('a2 -> 'a3) -> 'a2 bag -> ('a3, 'a1) join_ix -> ('a1,
      'a2) prod bag **)

  let rec match_ix eqK c b ix0 =
    match b with
    | Nil -> Nil
    | Cons (hd, b0) ->
      app (product (ix_get eqK ix0 (c hd)) (Cons (hd, Nil)))
        (match_ix eqK c b0 ix0)

  (** val equi_join :
      'a3 eqDec -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a1 bag -> 'a2 bag ->
      ('a1, 'a2) prod bag **)

  let equi_join h c1 c2 b1 b2 =
    match_ix h c2 b2 (build_ix h c1 b1)
 end


module type JoinParams = sig
  type l
  type r
  type k
  val lk : l -> k
  val rk : r -> k
  val eqL : l -> l -> bool
  val eqR : r -> r -> bool
  val eqK : k -> k -> bool
  val init_input : l bag * r bag
end

module JoinOp = functor (P : JoinParams) ->
 struct
  open P

  (** val f : (coq_L bag, coq_R bag) prod -> (coq_L, coq_R) prod bag **)

  let f x =
    EquiJoin.equi_join eqK lk rk (fst x) (snd x)

  type ('k, 'v) ix = ('k, 'v bag) dict

  type coq_ST = ((k, l) ix * (k, r) ix)

  (** val init :
      (coq_L bag, coq_R bag) prod -> ((coq_K, coq_L) EquiJoin.join_ix,
      (coq_K, coq_R) EquiJoin.join_ix) prod **)

  let init x =
    ((EquiJoin.build_ix eqK lk (fst x)),
      (EquiJoin.build_ix eqK rk (snd x)))

  (** val ix_union_bag :
      'a2 eqDec -> ('a1 -> 'a2) -> 'a1 bag -> ('a2, 'a1) EquiJoin.join_ix ->
      ('a2, 'a1) EquiJoin.join_ix **)

  let ix_union_bag =
    EquiJoin.build_ix_helper

  (** val ix_diff_bag :
      'a1 eqDec -> 'a2 eqDec -> ('a2 -> 'a1) -> ('a1, 'a2) EquiJoin.join_ix
      -> 'a2 bag -> ('a1, 'a2) EquiJoin.join_ix **)

  let ix_diff_bag =
    EquiJoin.ix_diff_bag

  (** val delta_ix :
      'a1 eqDec -> ('a1 -> coq_K) -> 'a1 bag_change -> (coq_K, 'a1) ix ->
      (coq_K, 'a1) ix **)

  let delta_ix h k delta_x st =
    match delta_x with
    | Bag_union b -> ix_union_bag eqK k b st
    | Bag_diff b -> ix_diff_bag eqK h k st b

  (** val delta_st :
      (coq_L bag, coq_R bag) prod delta_T -> coq_ST -> coq_ST **)

  let delta_st delta_x st =
    match delta_x with
    | Pair_fst delta_bl ->
      ((delta_ix eqL lk (delta_bl) (fst st)), (snd st))
    | Pair_snd delta_br ->
      ((fst st), (delta_ix eqR rk (delta_br) (snd st)))
    | Pair_both (delta_bl, delta_br) ->
      ((delta_ix eqL lk (delta_bl) (fst st)),
        (delta_ix eqR rk (delta_br) (snd st)))

  (** val ix_lookup :
      'a2 eqDec -> ('a2, 'a1) EquiJoin.join_ix -> 'a2 -> 'a1 bag **)

  let ix_lookup =
    EquiJoin.ix_get

  (** val join_ix :
      ('a2 -> coq_K) -> (coq_K, 'a1) ix -> 'a2 bag -> ('a1 bag -> 'a2 bag ->
      'a3 bag) -> 'a3 bag **)

  let join_ix k st b f0 =
    flat_map (fun x -> f0 (ix_lookup eqK st (k x)) (Cons (x, Nil))) b

  (** val delta_f_l :
      coq_L bag_change -> (coq_K, coq_R) ix -> (coq_L, coq_R) prod bag_change **)

  let delta_f_l delta_b st =
    match delta_b with
    | Bag_union b -> Bag_union (join_ix lk st b (fun b0 a -> product a b0))
    | Bag_diff b -> Bag_diff (join_ix lk st b (fun b0 a -> product a b0))

  (** val delta_f_r :
      coq_R bag_change -> (coq_K, coq_L) ix -> (coq_L, coq_R) prod bag_change **)

  let delta_f_r delta_b st =
    match delta_b with
    | Bag_union b -> Bag_union (join_ix rk st b product)
    | Bag_diff b -> Bag_diff (join_ix rk st b product)

  (** val delta_f :
      (coq_L bag, coq_R bag) prod delta_T -> coq_ST -> (coq_L, coq_R) prod
      bag_change list **)

  let delta_f delta_x st =
    match delta_x with
    | Pair_fst delta_bl ->
      Cons ((delta_f_l (delta_bl) (snd st)), Nil)
    | Pair_snd delta_br ->
      Cons ((delta_f_r (delta_br) (fst st)), Nil)
    | Pair_both (delta_bl, delta_br) ->
      Cons ((delta_f_l (delta_bl) (snd st)), (Cons
        ((delta_f_r (delta_br)
           (delta_ix eqL lk (delta_bl) (fst st))), Nil)))
 end
