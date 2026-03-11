open BagOps
open BagOp.Bag
open BagOp.Pair

(* Product (Select (_ < 10) r) (Select (_ > 20) q) *)

module S0Args = struct
  type a = int
  let cond x = x < 10
end
module S0 = SelectDiffOp(S0Args)

module S1Args = struct
  type a = int
  let cond x = x > 20
end
module S1 = SelectDiffOp(S1Args)

module PArgs = struct
  type t1 = int
  type t2 = int
  let eq1 x y = x = y
  let eq2 x y = x = y
  let init_input = (Nil, Nil)
end
module P = ProductDiffOp(PArgs)

module F = Base.Bin (S0)(S1)(P)

let change1 = (Pair_both (Bag_union (range 8  15), Bag_union (range 15  22)))
let out1 = F.dop change1

let change2 = Pair_snd (Bag_union (range 18 30))
let out2 = F.dop change2

let change3 = Pair_fst (Bag_diff (range 9 12))
let out3 = F.dop change3

let change4  = Pair_both (Bag_diff (range 13 14), Bag_diff (range 15 23))
let out4 = F.dop change4

let print_change = print_pair_change (print_bag_change print_int) (print_bag_change print_int)
let print_out = print_bag (print_bag_change (print_pair print_int print_int))

let print_step c o = print_string "  Input change:  "; print_change c; print_string "\n    ->\n  Output change: "; print_out o; print_string "\n\n\n"

let () = 
  print_string "Product (Select (_ < 10) r) (Select (_ > 20) q):\n";
  print_step change1 out1;
  print_step change2 out2;
  print_step change3 out3;
  print_step change4 out4
