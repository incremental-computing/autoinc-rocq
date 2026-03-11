open BagOps
open BagOp.Bag
open BagOp.Int

module P = struct
  let init_input = Nil
end

module JoinInt = struct
  let join x y = max x y
end

module PreOrd = struct
  type coq_E = int
  let eqa_dec x y = x = y
  let lta_dec x y = x < y
  let bottom = 0
end


module F = AggregateDiffOp(PreOrd)(JoinInt)(DiffInt)(P)
let change1 : int bag_change = Bag_union (range 1  15)
let out1 = F.dop change1

let change2 : int bag_change = Bag_union (range 18 30)
let out2 = F.dop change2

let change3 : int bag_change = Bag_diff (range 1 4)
let out3 = F.dop change3

let change4 : int bag_change = Bag_diff (range 5 13)
let out4 = F.dop change4

let change5 : int bag_change = Bag_diff (range 22 30)
let out5 = F.dop change5

let print_step c o = print_string "  Input change:  "; print_bag_change print_int c; print_string "\n    ->\n  Output change: "; print_int_change o; print_string "\n\n\n"

let () = 
  print_string "Aggregate\n";
  print_step change1 out1;
  print_step change2 out2;
  print_step change3 out3;
  print_step change4 out4;
  print_step change5 out5
