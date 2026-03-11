open BagOps
open BagOp.Bag
open Base
open BagOp.Pair
open BagOp.Int
open BagOp.Seq
open ExpSetup
open Rand

module S0Args = struct (* Select *)
  type a = int
  let cond x = x mod 10 = 0
end

module S1Args = struct (* Select *)
  type a = int
  let cond x = x mod 5 = 0
end

module S2Args = struct (* Join *)
  type l = int
  type r = int
  type k = int
  let lk x = x mod 500
  let rk x = x mod 1000
  let eqL x y = x = y
  let eqR x y = x = y
  let eqK x y = x = y
  let init_input = (Nil, Nil)
end

module S3Args = struct
  let init_input = Nil
end

module DiffInt = struct
  type delta_E = (int_change, int_change) pair_change
  let diff x y = 
    match x, y with
    | (x1, x2), (y1, y2) -> Pair_both (Shift (y1 - x1), Shift(y2 - x2))
end

module JoinMaxInt = struct
  let join x y = if x > y then x else y
end

module MaxPreOrd = struct
  type coq_E = int * int
  let eqa_dec x y = x = y
  let lta_dec x y = x < y
  let bottom = (0, 0)
end

module S = struct
  type a = int bag * int bag
  type b = int * int
  type da = (int bag_change, int bag_change) pair_change
  type db = (int_change, int_change) pair_change seq_change
  let input_size a = bag_size (fst a) + bag_size (snd a)
  let ph_in = pair_patch (bag_patch (=)) (bag_patch (=))
  let ph_out = seq_patch (pair_patch patch_int_change patch_int_change)
  let string_of_out x = "(" ^ string_of_int (fst x) ^ ", " ^ string_of_int (snd x) ^ ")"
  let filename = "./stat_agg_join.txt"
  let print_out_change = print_seq_change (print_pair_change (print_int_change) print_int_change)

  let init = (Nil, Nil)
  let eq_out a b = a = b
  let print_diff_out x y = Printf.printf "Inc result: (%d, %d), Non-inc result (%d, %d)\n" (fst x) (snd x) (fst y) (snd y) 
  let change_rate = ref 0.0
  let string_of_da = string_of_pair_change string_of_num_bag_change string_of_num_bag_change
  let string_of_db = string_of_bag (string_of_pair_change string_of_int_change string_of_int_change)
end

let clear_file fn = 
  let oc = open_out "./stat_agg_join.txt" in
  output_string oc ""; close_out oc


let gii a b = (range 1 a, range (a+1) b) (* generate initial input *)
let giic a b = Pair_both (Bag_union (range 1 a), Bag_union (range (a+1) b)) 

let pow2_list n = List.init n (fun i -> 1 lsl i)
let config p n = List.map (fun n -> (n * 1000, p)) (pow2_list n)
let res = 
  let _ = clear_file "./stat_join.txt" in
  List.map (fun (k, p) -> 
      let f() = let module M = EMake(Seq(Lift(AggregateDiffOp(MaxPreOrd)(JoinMaxInt)(DiffInt)(S3Args)))(Bin(SelectDiffOp(S0Args))(SelectDiffOp(S1Args))(JoinDiffOp(S2Args))))(S) in
      let h = k / 2 in
      let (rc_t, ic_t, m) = M.run ~p:p (gii h k, giic h k, (gen_bag_change_both p 1 h (h+1) k)) in
      (rc_t *. 1000.0, ic_t *. 1000.0, m) in
    let (rc_t1, ic_t1, m1) = f() in
    let (rc_t2, ic_t2, m2) = f() in
    let (rc_t3, ic_t3, m3) = f() in
    (k, (rc_t1 +. rc_t2 +. rc_t3) /. 3.0, (ic_t1 +. ic_t2 +. ic_t3) /. 3.0, (m1 +. m2 +. m3) /. 3.0)
  ) (config 0.01 7)
let _ = write_csv "./join_agg.csv" res
