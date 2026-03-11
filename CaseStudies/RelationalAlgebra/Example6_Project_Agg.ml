open BagOps
open BagOp.Bag
open BagOp.Pair
open BagOp.Int
open Base

module ProjParams = struct (* Projection params *)
  type a = int * int
  type b = int
  let g (x, y) = x + y 
end

module F = ProjectDiffOp(ProjParams)

module AggParams = struct (* Aggregation params *)
  let init_input = Nil
end

module JoinIntSum = struct
  let join x y = x + y
end

module JoinIntMax = struct
  let join x y = max x y
end


module PreOrd = struct
  type coq_E = int
  let eqa_dec x y = x = y
  let lta_dec x y = x < y
  let bottom = 0
end

module MAX = AggregateDiffOp(PreOrd)(JoinIntMax)(DiffInt)(AggParams)
module SUM = AggregateDiffOp(PreOrd)(JoinIntSum)(DiffInt)(AggParams)
module G = Seq(MAX)(F)
module H = Seq(SUM)(F)

let change1 = Bag_union (make_pair (range 1 5) (range 1 5))
let out1_max = G.dop change1
let out1_sum = H.dop change1


let change2 = Bag_union (make_pair (range 1 5) (range 1 5))
let out2_max = G.dop change2
let out2_sum = H.dop change2

let change3 = Bag_union (make_pair (range 3 5) (range 3 5))
let out3_max = G.dop change3
let out3_sum = H.dop change3

let print_in_change = print_bag_change (print_pair print_int print_int)
let print_out_change = print_int_change

let print_step c o = print_string "  Input change:  "; print_in_change c; print_string "\n    ->\n  Output change: "; print_out_change o; print_string "\n\n\n"

let () = 
  print_endline "Aggregation ((x, y) -> max x y) . Project ((x, y) -> x + y)\n";
  print_step change1 out1_max;
  print_step change2 out2_max;
  print_step change3 out3_max

let () = 
  print_endline "Aggregation ((x, y) -> x + y) . Project ((x, y) -> x + y)\n";
  print_step change1 out1_sum;
  print_step change2 out2_sum;
  print_step change3 out3_sum