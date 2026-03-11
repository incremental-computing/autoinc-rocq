open BagOp.Bag
open BagOp.Pair
let random_int lower upper =
  lower + Random.int (upper - lower + 1)
let gen_diff_bag p l u =
  if p < 0.0 || p > 1.0 then 
    invalid_arg ("The percentage " ^ string_of_float p ^ " is invalid")
  else if l > u then 
    invalid_arg ("The lower bound " ^ string_of_int l ^ " should be less or equal to the upper bound " ^ string_of_int u)
  else
    let (lf, uf) = (float_of_int l, float_of_int u) in
    let df = (uf -. lf +. 1.0) *. p in (* the number of elements to be generated*)
    let d = int_of_float df in
    let r = u - d in
    let g = random_int l r in
    Bag_diff (range g (g + d - 1))

let gen_union_bag p l u =
  if p < 0.0 || p > 1.0 then 
    invalid_arg ("The percentage " ^ string_of_float p ^ " is invalid")
  else if l > u then 
    invalid_arg ("The lower bound " ^ string_of_int l ^ " should be less or equal to the upper bound " ^ string_of_int u)
  else
    let (lf, uf) = (float_of_int l, float_of_int u) in
    let df = (uf -. lf +. 1.0) *. p in (* the number of elements to be generated*)
    let d = int_of_float df in
    let r = u + u - d in
    let g = random_int u r in
    Bag_union (range g (g + d - 1))

let gen_bag_change p l u =   
  let b = Random.bool() in
  if b then gen_union_bag p l u else gen_diff_bag p l u


let gen_bag_change_both p l1 u1 l2 u2 =
  Pair_both (gen_bag_change p l1 u1, gen_bag_change p l2 u2)


    