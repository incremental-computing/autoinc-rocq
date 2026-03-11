open Bag

(** val select : ('a1 -> bool) -> 'a1 bag -> 'a1 bag **)

let rec select f0 = function
| Nil -> Nil
| Cons (hd, tl) ->
  (match f0 hd with
   | true -> Cons (hd, (select f0 tl))
   | false -> select f0 tl)


module type SelectParams = sig type a;; val cond : a -> bool end

module IncSelect = functor ( P : SelectParams ) ->
 struct
  open P
  
  let f x =
    select cond x

  (** val delta_f : coq_T bag_change -> coq_T bag_change **)

  let delta_f = function
  | Bag_union b -> Bag_union (select cond b)
  | Bag_diff b -> Bag_diff (select cond b)
 end
