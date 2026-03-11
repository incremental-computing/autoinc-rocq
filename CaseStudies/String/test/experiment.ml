open Autoinc.Op
open Base

let float_to_string_2dp (f : float) : string =
  Printf.sprintf "%.2f" f
let round x =
  let f = 
    if x >= 0.0 then floor (x +. 0.5)
    else ceil (x -. 0.5) in
  Float.to_int f

let sum_floats lst = List.fold_left ( +. ) 0.0 lst
let avg_floats lst = let s = sum_floats lst in s /. Float.of_int (List.length lst) 

let stddev lst =
  let m = avg_floats lst in
  let variance =
    List.fold_left (fun acc x -> acc +. (x -. m) ** 2.) 0.0 lst
    /. float_of_int (List.length lst)
  in sqrt variance

let cartesian_product xs ys =
  List.flatten (
    List.map (fun x ->
      List.map (fun y -> (x, y)) ys
    ) xs
  )

let cartesian_product3 xs ys zs =
  List.concat_map (fun x ->
    List.concat_map (fun y ->
      List.map (fun z -> (x, y, z)) zs
    ) ys
  ) xs

let indexed_lines strs =
  strs
  |> List.mapi (fun i s -> Printf.sprintf "%d - %s" i s)
  |> String.concat "\n"

let range n = List.init n (fun i -> i)
let hashtbl_of_list lst =
  let tbl = Hashtbl.create (List.length lst) in
  List.iter (fun (k, v) -> Hashtbl.add tbl k v) lst;
  tbl

(* The experiment setup for a stateful differential operator *)
module type Setup =
 sig
  module OP : StatefulDiffOp
  (* description of each case of change, e.g. insertion before ... *)
  val change_cases : string list 
  (* a change generator takes an input and a change size, return a random input change  *)
  val change_generator : (int, OP.CA.t -> int -> OP.CA.dt) Hashtbl.t
  val size : OP.CA.t -> int
 end

module Make(M : Setup) = 
 struct
  open M
  open M.OP
  let exec s ds = 
    let init_output = f s in
    let init_state = init s in
    let inc () = df ds init_state  in
    let (output_change, ic_t) = timed inc in
    let non_inc () = f (CA.patch ds s) in
    let (recomp_output, rc_t) = timed non_inc in
    let inc_patch () = CB.patch output_change init_output in
    let (inc_output, ph_t) = timed inc_patch in
    assert (recomp_output = inc_output);
    (ic_t, ph_t, rc_t)

  (*
  run experiements with 
  - a given stateful differential operator
  - a given input
  - a given change rate (change size / input size) : int
  - a change generator (for each type) : input -> input change 
  - description of change type : int (the corresponding change description can be found in change cases)
  - repetition number
  output (string):
  change rate (%), change type (string), 
  incremental computation time, non-incremental computation time, speedup

  *)
  let run_once ~input ~rate ~gen = 
    let change_rate = Float.of_int rate /. 100. in
    let input_size = size input in
    let change_size = round (Float.of_int input_size *. change_rate) in
    let input_change = gen input change_size in
    let (ic_t, ph_t, rc_t)= exec input input_change in
    (ic_t, ph_t, rc_t)
  


  let run_n_time (input, rate, gen, rep) =
    let res = List.init rep (fun _ -> run_once ~input ~rate ~gen) in
    let ic_ts = avg_floats (List.map (fun (x, y, z) -> x) res) in
    let ph_ts = avg_floats (List.map (fun (x, y, z) -> y) res) in
    let rc_ts = avg_floats (List.map (fun (x, y, z) -> z) res) in
    let ic_ts_stdev = stddev (List.map (fun (x, y, z) -> x *. 1_000_000.) res) in
    let ph_ts_stdev = stddev (List.map (fun (x, y, z) -> y *. 1_000_000.) res) in
    let rc_ts_stdev = stddev (List.map (fun (x, y, z) -> z *. 1_000_000.) res) in
    let speedup = rc_ts /. ic_ts in
    (rate, time_to_string ic_ts, time_to_string ph_ts, time_to_string rc_ts, 
    float_to_string_2dp speedup, float_to_string_2dp ic_ts_stdev, float_to_string_2dp ph_ts_stdev,float_to_string_2dp rc_ts_stdev, speedup)
  
  let group_by (ts : float list) groups = 
    let group = List.map (List.map (List.nth ts)) groups in 
    List.map (fun l -> (sum_floats l) /. Float.of_int (List.length l)) group  

  let dump_res input_size ctype (rate, ic_t, ph_t, rc_t, speedup, ic_dev, ph_dev, rc_dev, _) = 
    Int.to_string input_size ^ "," ^ Int.to_string ctype ^ "," ^ Int.to_string rate ^ "," ^  
      ic_t ^ "," ^ ph_t ^ "," ^ rc_t ^ "," ^ speedup ^ "," ^ ic_dev ^ "," ^ rc_dev 

  let dump_res_simp input_size ctype (rate, ic_t, ph_t, rc_t, speedup, ic_dev, ph_dev, rc_dev, _) = 
    Int.to_string ctype ^ "," ^ Int.to_string rate ^ "," ^ speedup


  let gen_filename opname rate rep = opname ^ "_" ^ Int.to_string rate ^ "_" ^ Int.to_string rep

  let dump (opname, input, rate, ctype, rep) =
    let (rate, ic_ts, ph_ts, rc_ts, speedup, ic_dev, ph_dev, rc_dev, speedup_num) = 
       run_n_time (input, rate, Hashtbl.find M.change_generator ctype, rep) in
    let oc = open_out (gen_filename opname rate rep) in 
    let column_name = "change,rate(%),ic_t,rc_t,speedup,ic_dev,rc_dev\n" in
    let s = dump_res (size input) ctype (rate, ic_ts, ph_ts, rc_ts, speedup, ic_dev, ph_dev, rc_dev, speedup_num)
    in output_string oc (column_name ^ s) ; close_out oc


  let run_benchmark op_name input ctypes rates rep =
    let setup = cartesian_product ctypes rates in
    let results = List.map (fun (ctype, rate) -> 
      (size input, ctype, run_n_time (input, rate, Hashtbl.find M.change_generator ctype, rep))) setup in
    let stats = List.map (fun (x, y, z) -> dump_res_simp x y z) results in 
    let oc = open_out (op_name ^ ".txt") in
    let description = indexed_lines change_cases in
    (* let column = "size,change,rate(%),ic_t,rc_t,speedup,ic_dev,rc_dev\n" in *)
    let column = "change,rate(%),speedup\n" in
    let s = String.concat "\n" stats in
    output_string oc (description ^ "\n\n\n" ^ column ^ s); close_out oc;
    List.map (fun (_, _, (_, _, _, _, _, _, _, _, d)) -> d) results 
 end