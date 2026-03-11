open Base

module type Dump = sig
  module DOP : DiffOp
  open DOP
  val description : string
  val init : a ref
  val in_ph : da -> a -> a
  val print_in : a -> unit
  val print_out : b -> unit
  val print_in_change : da -> unit
  val print_out_change : db -> unit
end

module Make = functor (D : Dump) -> struct
  open D
  open D.DOP

  (* 
  This function receives an input change and prints 
  - db : output change
  - t_inc : elapsed time for computing the output change (via dop)
  - b : output
  - t_non_inc : elapsed time for computing the output (via op)
  - speedup: t_non_inc / t_inc
  *)
  let print_step c pda pdb pb  = 
    print_endline "**************************************************";
    let () = if pda then begin
      print_string "Input change: ";
      print_in_change c;
      print_string "\n";
      print_endline "------------------------------------------------"
    end in
    print_endline "Incremental run";
    let inc () = dop c in
    let (db, t_inc) = timed inc in
    let () = if pdb then begin
      print_string "Output change: ";
      print_out_change db;
      print_string "\n";
    end in Printf.printf "Elapsed time: %F\n" t_inc;
    print_endline "------------------------------------------------";
    print_endline "Non-incremental run";
    init := in_ph c !init; (* update the input *)
    let non_inc () = op !init in
    let (b, t_non_inc) = timed non_inc in
    let () = if pb then begin
      Printf.printf "Output: ";
      print_out b;
      print_string "\n"
    end in
    Printf.printf "Elapsed time: %F\n" t_non_inc;
    print_endline "------------------------------------------------";
    Printf.printf "Speedup: %F\n" (Float.div t_non_inc t_inc);
    print_endline "**************************************************";
    print_endline "\n\n"

  let rec print_steps cs pda pdb pb =
    match cs with
    | [] -> print_endline "Computation finished!"
    | c :: cs -> print_step c pda pdb pb; print_steps cs pda pdb pb

  let print_stat s ?(pda=true) ?(pdb=true) ?(pb=true) () = 
    print_endline "\n";
    print_endline "***********************************************************";
    print_endline "********************** Statistics *************************";
    print_endline "***********************************************************";
    print_string "\n";
    print_endline description;
    Printf.printf "Initial input: ";
    print_in !init;
    print_string "\n"; 
    Printf.printf "Initial output: ";
    let o = op !init in
    print_out o;
    print_string "\n";
    let cur_init = !init in
    print_steps s pda pdb pb;
    init := cur_init
end