
open Bag
open Pair

(** val union_all : 'a1 list -> 'a1 list -> 'a1 bag **)

let union_all =
  app

module type UnionAllParams = sig
  type a
end

module IncUnionAll = functor (P : UnionAllParams) ->
 struct
  (* open P *)

  (** val f : (coq_T list, coq_T list) prod -> coq_T bag **)

  let f = function
  | (b1, b2) -> union_all b1 b2

  (** val delta_f : delta_pair -> delta_seq **)

  let delta_f c =
    match c with
    | Pair_fst c0 -> (Cons (c0, Nil))
    | Pair_snd c0 -> (Cons (c0, Nil))
    | Pair_both (c1, c2) -> (Cons (c1, (Cons (c2, Nil))))
 end
