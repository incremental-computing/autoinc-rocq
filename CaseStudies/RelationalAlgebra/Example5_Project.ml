open BagOps
open BagOp.Bag
open BagOp.Pair

module P = struct
  type a = int * int
  type b = int
  let g (x, y) = x + y 
end

module F = ProjectDiffOp(P)

let change1 = Bag_union (make_pair (range 1 5) (range 6 10))
let out1 = F.dop change1

let change2 = Bag_diff (Cons ((1, 6), Cons ((4, 7), Nil)))
let out2 = F.dop change2

let print_in_change = print_bag_change (print_pair print_int print_int)
let print_out_change = print_bag_change print_int

let print_step c o = print_string "  Input change:  "; print_in_change c; print_string "\n    ->\n  Output change: "; print_out_change o; print_string "\n\n\n"

let () = 
  print_endline "Project ((x, y) -> x + y) b";
  print_step change1 out1;
  print_step change2 out2
