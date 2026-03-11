
open Bag
open Pair

let empty_map () = Hashtbl.create 1000

let dict_add_with key value f map =
  let _ = match Hashtbl.find_opt map key with
  | Some existing_value -> 
      Hashtbl.replace map key (f existing_value)
  | None -> 
      Hashtbl.add map key value in
  map
type 't bag = 't list

let rec product b1 b2 =
  match b1 with
  | Nil -> Nil
  | Cons (hd, tl) -> app (map (fun x -> (hd, x)) b2) (product tl b2)

module EquiJoin =
 struct
  let ix_diff_elem eqT c d t =
    match Hashtbl.find_opt d (c t) with
    | None -> d
    | Some v -> Hashtbl.replace d (c t) (list_del eqT v t); d

  let ix_diff_bag eqT c d b =
    fold_left (ix_diff_elem eqT c) b d

  let update_ix c d a = dict_add_with (c a) (Cons (a, Nil)) (fun x -> Cons (a, x)) d

  let ix_get d k = match Hashtbl.find_opt d k with
  | None -> Nil
  | Some v -> v

  let build_ix_helper c b init0 =
    fold_left (update_ix c) b init0

  let build_ix c b = build_ix_helper c b (empty_map())

  let rec match_ix c b ix0 =
    match b with
    | Nil -> Nil
    | Cons (hd, b0) ->
      app (product (ix_get ix0 (c hd)) (Cons (hd, Nil)))
        (match_ix c b0 ix0)

  let equi_join h c1 c2 b1 b2 =
    match_ix c2 b2 (build_ix c1 b1)
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
  let f x =
    EquiJoin.equi_join eqK lk rk (fst x) (snd x)

  let init x =
    ((EquiJoin.build_ix lk (fst x)),
      (EquiJoin.build_ix rk (snd x)))

  let ix_union_bag =
    EquiJoin.build_ix_helper

  let ix_diff_bag =
    EquiJoin.ix_diff_bag

  let delta_ix h k delta_x st =
    match delta_x with
    | Bag_union b -> ix_union_bag k b st
    | Bag_diff b -> ix_diff_bag h k st b

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
    flat_map (fun x -> f0 (ix_lookup st (k x)) (Cons (x, Nil))) b

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
