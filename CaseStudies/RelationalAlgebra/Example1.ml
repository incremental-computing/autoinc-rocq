open BagOps
open BagOp.Bag

(* Select (_ < 20) (Select (_ > 10) r) *)

module S0Args = struct
  type a = int
  let cond x = x > 10
end
module S0 = SelectDiffOp(S0Args)

module S1Args = struct
  type a = int
  let cond x = x < 20
end
module S1 = SelectDiffOp(S1Args)

module F = Base.Seq (S0)(S1)


let change1 : int bag_change = Bag_union (range 1  15)
let out1 : int bag_change = F.dop change1

let change2 : int bag_change = Bag_union (range 18 30)
let out2 : int bag_change = F.dop change2

let change3 : int bag_change = Bag_diff (range 1 4)
let out3 : int bag_change = F.dop change3

let change4 : int bag_change = Bag_diff (range 5 13)
let out4 : int bag_change = F.dop change4

let print_step c o = print_string "  Input change:  "; print_bag_change print_int c; print_string "\n    ->\n  Output change: "; print_bag_change print_int o; print_string "\n\n\n"

let () = 
  print_string "Select (_ > 10) r:\n";
  print_step change1 out1;
  print_step change2 out2;
  print_step change3 out3;
  print_step change4 out4
