(* 
Example for join
*)

open BagOps
open BagOp.Bag
open BagOp.Pair

module Params = struct
  type l = int
  type r = int
  type k = int
  let lk x = x mod 5
  let rk x = x mod 5
  let eqL x y = x = y
  let eqR x y = x = y
  let eqK x y = x = y
  let init_input = (Nil, Nil)
end
module F = JoinDiffOp(Params)

let change1 = (Pair_both (Bag_union (range 8  15), Bag_union (range 15  22)))
let out1 = F.dop change1
let change2 = (Pair_both (Bag_union (range 2  4), Bag_union (range 8  10)))
let out2 = F.dop change2
let change3 = (Pair_both (Bag_union (range 8  12), Bag_union (range 3  5)))
let out3 = F.dop change3

let print_change = print_pair_change (print_bag_change print_int) (print_bag_change print_int)
let print_out = print_bag (print_bag_change (print_pair print_int print_int))

let print_step c o = print_string "  Input change:  "; print_change c; print_string "\n    ->\n  Output change: "; print_out o; print_string "\n\n\n"

let () = 
  print_string "Join (Find the common elements in both bags)\n";
  print_step change1 out1;
  print_step change2 out2;
  print_step change3 out3