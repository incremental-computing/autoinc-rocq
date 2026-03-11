open Bag

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f0 = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f0 a), (map f0 l0))

(** val bag_map : ('a1 -> 'a2) -> 'a1 bag -> 'a2 bag **)

let bag_map = map

module type ProjectParams = sig
  type a
  type b
  val g : a -> b
end

module IncProject (P : ProjectParams) =
 struct
  open P

  let f x = bag_map g x

  let delta_f = function
  | Bag_union b -> Bag_union (bag_map g b)
  | Bag_diff b -> Bag_diff (bag_map g b)
 end
