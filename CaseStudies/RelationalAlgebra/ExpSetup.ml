(* This file defines a module type that defines the setup for an experiment. *)
open Base

let memory_usage () = let stats = Gc.stat () in
  (float_of_int stats.Gc.heap_words *. float_of_int (Sys.word_size / 8) /. (1024.0 *. 1024.0))

module type Setup = sig
  type a
  type b
  type da
  type db
  val input_size : a -> int
  val ph_in : da -> a -> a
  val ph_out : db -> b -> b
  val print_out_change : db -> unit
  val filename : string
  val init : a
  val eq_out : b -> b -> bool
  val print_diff_out : b -> b -> unit
  val change_rate : float ref
  val string_of_da : da -> string
  val string_of_db : db -> string
end

module EMake = functor (D : DiffOp) (S : Setup with type a = D.a with type b = D.b with type da = D.da with type db = D.db) -> struct
  open S
  let exec a dinit da = 
    let init_inc () = D.dop dinit in  (* initialize the state *)
    let (oc_init, ic_init_t) = timed init_inc in
    let inc () = D.dop da in
    let (oc, ic_t) = timed inc in
    let non_inc () = D.op (ph_in da a) in
    let (_, rc_t) = timed non_inc in
    let m = memory_usage () in
    (rc_t, ic_init_t, ic_t, string_of_db oc, m)

  let exec_with_test_eq a dinit da = 
    let o_init = D.op init in (* initial output *)
    let init_inc () = D.dop dinit in  (* initial output change *)
    let (oc_init, ic_init_t) = timed init_inc in
    let inc () = D.dop da in
    let (oc, ic_t) = timed inc in
    let ic_o = ph_out oc (ph_out oc_init o_init) in
    let non_inc () = D.op (ph_in da a) in
    let (rc_o, rc_t) = timed non_inc in
    if not (eq_out ic_o rc_o) then 
      let () = print_endline (string_of_da dinit) in
      let () = print_diff_out ic_o rc_o in
      let () = print_endline (string_of_da da) in
      invalid_arg "The result of incremental computation and non-incremental computation is not equal!"
    else 
      (rc_t, ic_init_t, ic_t, string_of_db oc)

  let dump a dinit da =
    let (rc_t, ic_init_t, ic_t, oc_dec, m) = exec a dinit da in
    let oc = open_out_gen [Open_append; Open_creat] 0o666 filename in    
    let s = "Input size : " ^ string_of_int (input_size a) ^ "\n" ^
            "Input change : " ^ string_of_da da ^ "\n" ^
            "Input change size (%) : " ^ string_of_float (!change_rate *. 100.0) ^ "% \n" ^
            "Output change size : " ^ oc_dec ^ " \n" ^
            "Memory usage: " ^ string_of_float m ^ "\n" ^
            "Incremental computation : \n" ^ 
            (* "\tResult : " ^ string_of_out ic_o ^ "\n" ^ *)
            "\tInit state time: " ^ string_of_float ic_init_t ^ "\n" ^
            "\tTime: " ^ string_of_float ic_t ^ "\n" ^
            "Recomputation : \n" ^ 
            (* "\tResult : " ^ string_of_out rc_o ^ "\n" ^ *)
            "\tTime: " ^ string_of_float rc_t ^ "\n" ^
            "Speedup : " ^ string_of_float (Float.div rc_t ic_t) ^ "\n\n\n"   
    in output_string oc s;
    close_out oc; (rc_t, ic_t, m)

  let run ?(p=0.0) x = let (a, dinit, da) = x in change_rate := p; dump a dinit da
end
let clear_file fn = 
  let oc = open_out fn in
  output_string oc ""; close_out oc
let write_csv filename data =
  let _ = clear_file filename in
  let oc = open_out filename in
  Printf.fprintf oc "size,rc_t,ic_t,memory\n"; (* Write header *)
  List.iter (fun (s, x, y, m) -> Printf.fprintf oc "%d,%f,%f,%f\n" s x y m) data;
  close_out oc