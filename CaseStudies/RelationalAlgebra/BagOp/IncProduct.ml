
open Bag
open Pair

(* 
type 't change =
  __ -> 't -> __ -> 't
  (* singleton inductive, whose constructor was Build_change *)

(** val patch : 'a1 change -> 'a1 delta_T -> 'a1 -> 'a1 **)

let patch c delta_t t =
  c delta_t t __ *)


(** val union_all : 'a1 list -> 'a1 list -> 'a1 bag **)

let union_all =
  app

(** val product : 'a1 bag -> 'a2 bag -> ('a1, 'a2) prod bag **)

let rec product b1 b2 =
  match b1 with
  | Nil -> Nil
  | Cons (hd, tl) -> app (map (fun x -> (hd, x)) b2) (product tl b2)


module type ProductParams = sig 
  type t1
  type t2
  val eq1 : t1 -> t1 -> bool
  val eq2 : t2 -> t2 -> bool
  val init_input : (t1 bag * t2 bag)
end

module IncProduct = functor (P : ProductParams) ->
 struct
  open P

  type coq_A = (t1 bag * t2 bag)

  type coq_B = (t1 * t2) bag

  (** val f : coq_A -> coq_B **)

  let f = function
  | (a, b) -> product a b

  type coq_ST = coq_A

  (** val init : coq_A -> coq_A **)

  let init = id

  (** val df_x :
      coq_T1 bag_change -> coq_T2 bag -> (coq_T1, coq_T2) prod bag_change **)

  let df_x delta_x y =
    match delta_x with
    | Bag_union b -> Bag_union (product b y)
    | Bag_diff b -> Bag_diff (product b y)

  (** val df_y :
      coq_T2 bag_change -> coq_T1 bag -> (coq_T1, coq_T2) prod bag_change **)

  let df_y delta_y x =
    match delta_y with
    | Bag_union b -> Bag_union (product x b)
    | Bag_diff b -> Bag_diff (product x b)

  (** val delta_f :
      (coq_T1 bag, coq_T2 bag) prod delta_T -> coq_ST -> (coq_T1, coq_T2)
      prod bag delta_T **)

  let delta_f delta_t = function
  | (x, y) ->
    (match delta_t with
     | Pair_fst c ->
       let c0 = c in (Cons ((df_x c0 y), Nil))
     | Pair_snd c ->
       let c0 = c in (Cons ((df_y c0 x), Nil))
     | Pair_both (c1, c2) ->
       let c3 = c1 in
       let c4 = c2 in
       let c1' = df_x c3 y in
       let x' = bag_patch eq1 (c3) x in
       let c2' = df_y c4 x' in (Cons (c1', (Cons (c2', Nil)))))

  (** val delta_st :
      (coq_T1 bag, coq_T2 bag) prod delta_T -> coq_ST -> coq_ST **)

  let delta_st delta_t = function
  | (x, y) ->
    (match delta_t with
     | Pair_fst c -> ((bag_patch eq1 c x), y)
     | Pair_snd c -> (x, (bag_patch eq2 c y))
     | Pair_both (c1, c2) ->
       ((bag_patch eq1 c1 x), (bag_patch eq2 c2 y)))
 end
