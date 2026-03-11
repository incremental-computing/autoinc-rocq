open Autoinc.Op

(* let timed (f : unit -> 'a) : 'a * float =
  Gc.full_major();
  let start = Sys.time () in
  let result = f () in
  let finish = Sys.time () in
  (result, finish -. start) *)

let timed (f : unit -> 'a) : 'a * float =
  let c = Mtime_clock.counter () in
  let res   = f () in
  let span  = Mtime_clock.count c in
  let msecs  = Int64.to_float (Mtime.Span.to_uint64_ns span) /. 1e6 in
  (res, msecs)         (* returns nanoseconds directly *)



let time_to_string t = Printf.sprintf "%.2f" (t *. 1_000_000.)

module type DiffOpTest = sig
  module D : StatefulDiffOp
  open D
  val test_cases : (CA.t * CA.dt) list 
end

module Make(S : DiffOpTest) = struct
  open S
  open D
  let test_diff_op (s, ds) = 
    print_endline ("Initial input: " ^ CA.v_to_string s);
    print_endline ("Input change: " ^ CA.dv_to_string ds);
    let updated_input = CA.patch ds s in
    print_endline ("Updated input: " ^ CA.v_to_string updated_input);
    let init_output = f s in
    print_endline ("Initial output: " ^ CB.v_to_string init_output);
    let init_state = init s in
    print_endline ("Initial state: " ^ CS.v_to_string init_state);
    let inc () = df ds init_state  in
    let (output_change, ic_t) = timed inc in
    print_endline ("[" ^ Float.to_string (ic_t *. 1_000_000.) ^ "µs]" ^ "Output change: " ^ CB.dv_to_string output_change);
    let non_inc () = f updated_input in
    let (recomp_output, nc_t) = timed non_inc in
    print_endline ("[" ^ Float.to_string (nc_t *. 1_000_000.) ^ "µs]" ^ "Recomputation: " ^ CB.v_to_string recomp_output);
    let inc_output = CB.patch output_change init_output in
    print_endline ("Incremental computation: " ^ CB.v_to_string inc_output);
    let updated_state = CS.patch ds init_state in
    assert (recomp_output = inc_output);
    print_endline ("Updated state: " ^ CS.v_to_string updated_state);
    print_endline "-------------------------------------------------";
    print_endline ""

  let exec (s, ds) = 
    let updated_input = CA.patch ds s in
    let init_output = f s in
    let init_state = init s in
    let inc () = df ds init_state  in
    let (output_change, ic_t) = timed inc in
    let non_inc () = f updated_input in
    let (recomp_output, nc_t) = timed non_inc in
    let inc_output = CB.patch output_change init_output in
    assert (recomp_output = inc_output);
    ()
  let run_tests () = List.iter test_diff_op S.test_cases 
end

let read_file_to_string filename =
  In_channel.with_open_bin filename In_channel.input_all
