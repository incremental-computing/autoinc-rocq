open Bag

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b


(* type 'a option =
| Some of 'a
| None *)


(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f0 a0 = function
| Nil -> a0
| Cons (b, t) -> f0 b (fold_right f0 a0 t)


module type Difference = sig
  type t
  type delta_t
  val diff : t -> t -> delta_t
 end

(** val le_lt_dec : nat -> nat -> sumbool **)

let rec le_lt_dec n m =
  match n with
  | O -> true
  | S n0 -> (match m with
             | O -> false
             | S n1 -> le_lt_dec n0 n1)
(** val le_gt_dec : nat -> nat -> sumbool **)

let le_gt_dec =
  le_lt_dec

(** val le_dec : nat -> nat -> sumbool **)

let le_dec =
  le_gt_dec

(** val lt_dec : nat -> nat -> sumbool **)

let lt_dec n m =
  le_dec (S n) m


module type STRICT_PRE_ORDER =
 sig
  type coq_E

  val eqa_dec : coq_E -> coq_E -> bool

  val lta_dec : coq_E -> coq_E -> bool

  val bottom : coq_E
 end

module AggregateTree =
 functor (PreOrd:STRICT_PRE_ORDER) ->
 functor (Join:sig
  val join : PreOrd.coq_E -> PreOrd.coq_E -> PreOrd.coq_E
 end) ->
 struct
  type coq_AT =
  | Empty
  | Node of PreOrd.coq_E * PreOrd.coq_E * nat * int * coq_AT * coq_AT

  let rec print_tree_helper space p = function
  | Empty -> print_endline (space ^ "Empty")
  | Node (res, elem, count0, h, l, r) ->
    print_string (space ^ "Result: "); p res;
    print_string "; elem: "; p elem;
    print_string "\n";
    print_tree_helper ("  " ^ space) p l; print_tree_helper ("  " ^ space) p r

  let print_tree p = print_tree_helper "" p
  (** val coq_AT_rect :
      'a1 -> (PreOrd.coq_E -> PreOrd.coq_E -> nat -> coq_AT -> 'a1 -> coq_AT
      -> 'a1 -> 'a1) -> coq_AT -> 'a1 **)

  let rec coq_AT_rect f0 f1 = function
  | Empty -> f0
  | Node (res, elem, count0, _, l, r) ->
    f1 res elem count0 l (coq_AT_rect f0 f1 l) r (coq_AT_rect f0 f1 r)

  (** val coq_AT_rec :
      'a1 -> (PreOrd.coq_E -> PreOrd.coq_E -> nat -> coq_AT -> 'a1 -> coq_AT
      -> 'a1 -> 'a1) -> coq_AT -> 'a1 **)

  let rec coq_AT_rec f0 f1 = function
  | Empty -> f0
  | Node (res, elem, count0, _, l, r) ->
    f1 res elem count0 l (coq_AT_rec f0 f1 l) r (coq_AT_rec f0 f1 r)

  (** val result : coq_AT -> PreOrd.coq_E **)

  let result = function
  | Empty -> PreOrd.bottom
  | Node (res, _, _, _, _, _) -> res

  (** val node : PreOrd.coq_E -> nat -> coq_AT -> coq_AT -> coq_AT **)

  let height = function
  | Empty -> 0
  | Node (_, _, _, h, _, _) -> h

  let factor = function 
  | Empty -> 0
  | Node (_, _, _, _, l, r) -> height l - height r

  let rotateLeft = function 
  | Node (res, elem, count, _, l , 
      Node (_, r_elem, r_count, _, r_l, r_r)) -> 
      let new_l = Node((Join.join elem (Join.join (result l) (result r_l))), elem, count, 
          1 + (max (height l) (height r_l)), l, r_l) in
      Node(res, r_elem, r_count, 1 + (max (height new_l) (height r_r)), new_l, r_r)
  | n -> n

  let rotateRight = function 
  | Node (res, elem, count, _, 
      Node (_, l_elem, l_count, _, l_l, l_r) , 
      r) -> 
      let new_r = Node((Join.join elem (Join.join (result l_r) (result r))), elem, count, 
          1 + (max (height l_r) (height r)), l_r, r) in
      Node(res, l_elem, l_count, 1 + (max (height l_l) (height new_r)), l_l, new_r)
  | n -> n


  let rotateRight = function 
  | Empty -> Empty
  | Node (res, elem, count, h, l , r) -> Node (res, elem, count, h, l , r)
    
  let rec elem_join e n = match n with
  | O -> PreOrd.bottom
  | S O -> e
  | S n -> Join.join e (elem_join e n)

  let node elem count0 l r =
    let res = (Join.join (elem_join elem count0) (Join.join (result l) (result r))) in
    let n = Node (res, elem, count0, 1 + (max (height l) (height r)), l, r) in
    let n_fac = factor n in
    if (n_fac > 1) then (
      if (factor l > 0) then
        rotateRight(n)
      else (
        let l_rot = rotateLeft(l) in
        let n_rot = Node (res, elem, count0, 1 + (max (height l_rot) (height r)), l_rot, r) in
        rotateRight(n_rot)
      )
    )
    else if (n_fac < -1) then (
      if (factor r < 0) then
        rotateLeft(n)
      else (
        let r_rot = rotateRight(r) in
        let n_rot = Node (res, elem, count0, 1 + (max (height l) (height r_rot)), l, r_rot) in
        rotateLeft(n_rot)
      )
    )
    else 
      n


  (** val insert : coq_AT -> PreOrd.coq_E -> coq_AT **)

  let rec insert t x =
    match t with
    | Empty -> Node (x, x, (S O), 1, Empty, Empty)
    | Node (res, elem, c, h, l, r) ->
      (match PreOrd.eqa_dec x elem with
       | true -> node elem (S c) l r
       | false ->
         (match PreOrd.lta_dec x elem with
          | true -> node elem c (insert l x) r
          | false -> node elem c l (insert r x)))

  (** val delete_min :
      coq_AT -> ((PreOrd.coq_E, nat) prod, coq_AT) prod option **)

  let rec delete_min = function
  | Empty -> None
  | Node (_, elem, c, _, l, r) ->
    (match l with
     | Empty -> Some (Pair ((Pair (elem, c)), r))
     | Node (_, _, _, _, _, _) ->
       (match delete_min l with
        | Some p ->
          let Pair (p0, l') = p in Some (Pair (p0, (node elem c l' r)))
        | None -> None))

  (** val delete_root : coq_AT -> coq_AT **)

  let delete_root = function
  | Empty -> Empty
  | Node (_, _, _, _, l, r) ->
    (match r with
     | Empty -> l
     | Node (_, _, _, _, _, _) ->
       (match delete_min r with
        | Some p ->
          let Pair (p0, r') = p in let Pair (m, c) = p0 in node m c l r'
        | None -> r))

  (** val delete : coq_AT -> PreOrd.coq_E -> coq_AT **)

  let rec delete t x =
    match t with
    | Empty -> t
    | Node (res, elem, c, h, l, r) ->
      (match PreOrd.eqa_dec x elem with
       | true ->
         (match lt_dec (S O) c with
          | true -> node elem (pred c) l r
          | false -> delete_root t)
       | false ->
         (match PreOrd.lta_dec x elem with
          | true -> node elem c (delete l x) r
          | false -> node elem c l (delete r x)))

  (** val count : PreOrd.coq_E -> coq_AT -> nat **)

  let rec count x = function
  | Empty -> O
  | Node (_, elem, c, _, l, r) ->
    (match PreOrd.eqa_dec x elem with
     | true -> c
     | false ->
       (match PreOrd.lta_dec x elem with
        | true -> count x l
        | false -> count x r))
 end


module DatalogAggregation =
 functor (PreOrd:STRICT_PRE_ORDER) ->
 functor (Join:sig
  val join : PreOrd.coq_E -> PreOrd.coq_E -> PreOrd.coq_E
 end) ->
  functor (Diff:sig
    type delta_E
    val diff : PreOrd.coq_E -> PreOrd.coq_E -> delta_E
  end) ->
 struct
  module Agg = AggregateTree(PreOrd)(Join)

  (** val coq_DiffE : PreOrd.coq_E Difference.difference **)

  type coq_A = PreOrd.coq_E bag

  type coq_ST = Agg.coq_AT

  (** val init : coq_A -> Agg.coq_AT **)

  let init t =
    fold_left Agg.insert t Agg.Empty

  (** val delta_st : PreOrd.coq_E bag delta_T -> coq_ST -> coq_ST **)

  let delta_st delta_t st =
    match delta_t with
    | Bag_union b -> fold_left Agg.insert b st
    | Bag_diff b -> fold_left Agg.delete b st

  (** val f : PreOrd.coq_E list -> PreOrd.coq_E **)

  let f =
    fold_right Join.join PreOrd.bottom

  (** val delta_f :
      PreOrd.coq_E bag delta_T -> coq_ST -> PreOrd.coq_E delta_T **)

  let delta_f delta_t st =
    let st' = delta_st delta_t st in
    Diff.diff (Agg.result st) (Agg.result st')
 end
