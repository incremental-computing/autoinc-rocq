open Diffop_experiment
open Autoinc.String_op
open Autoinc.Opbase
open Rand

(* the change type of lastIndexOf *)
let lio_ct = 
  [ "Insertion before the occurence (best case)"
  ; "deletion before the occurence (best case)"
  ; "deletion after the occurence (best case)"
  ; "The character is not found before doing deletion (best case)"
  ; "The deleted string contains the last occurrence of the character (worst case)"
  ; "The character does not exist before, then do insertion (intermediate case)"
  ; "insertion after the last occurence  (intermediate case)"
  ]

(* Insertion before the occurence (best case) *)
let change_generator_0 index s = gen_ins_at (0, index)

(* deletion before the occurence (best case) *)
let change_generator_1 index s = gen_del_at (0, index)
 
(* deletion after the occurence (best case) *)
let change_generator_2 index s = gen_del_at (index+1, List.length s)

(* The character is not found before doing deletion (best case) *)
let change_generator_3 s size = 
  gen_del_at (0, List.length s) size 

(* The deleted string contains the last occurrence of the character (worst case) *)
let change_generator_4 index s size =
  let h = size / 2 in
    del (max (index - h) 0) (min (index + h) (List.length s)) 

(* The character does not exist before, then do insertion (intermediate case) *)
let change_generator_5 s = gen_ins_at (0, List.length s)

(* insertion after the last occurence  (intermediate case) *)
let change_generator_6 index s = gen_ins_at (index+1, List.length s)


    
module type Generator = sig
  val generators : (int, char list -> int -> DString.dt) Hashtbl.t
end

module LastIndexOfSetup(C : Char)(G : Generator) = struct
  module OP = StatefulFunctorSingleFun(StringLastIndexOfSingleFun(C))
  let change_cases = lio_ct
  let change_generator = G.generators

  let size = List.length
end

let paragraph = string_to_list (Base.read_file_to_string "./test/resources/lastIndexOf/paragraph.txt")
let page = string_to_list (Base.read_file_to_string "./test/resources/lastIndexOf/page.txt")

(* let () = match last_index_of page '%' with
| Some k -> print_endline (Int.to_string k)
| None -> print_endline "None" *)


let make_char (ch : char) : (module Char) = 
  let module C = struct
    let c = ch
  end in
  (module C : Char)
  

let param_generator k = [
  (0, change_generator_0 k)
; (1, change_generator_1 k)
; (2, change_generator_2 k)
; (4, change_generator_4 k)
; (6, change_generator_6 k)
]

let non_param_generator = [
  (3, change_generator_3)
; (5, change_generator_5)
]

let paragraph_gen = hashtbl_of_list (param_generator 397 @ non_param_generator)
let page_gen = hashtbl_of_list (param_generator 2820 @ non_param_generator)

let run_benchmark ~filename ~input ~ctypes ~ch ~generators = 
  let (module C : Char) = make_char(ch) in 
  let module M : Generator = struct let generators = generators end in
  let module A = Make(LastIndexOfSetup(C)(M))(DString)(DOption(DNat)) in
  A.run_benchmark filename input ctypes [1; 5; 10] 100


(* let () = run_benchmark 
  ~filename:"last_index_of_paragraph_01246" 
  ~input:paragraph 
  ~ch:'d' 
  ~ctypes:[0;1;2;4;6]
  ~generators: paragraph_gen

let () = run_benchmark 
  ~filename:"last_index_of_paragraph_35" 
  ~input:paragraph 
  ~ch:'%' 
  ~ctypes:[3;5]
  ~generators: paragraph_gen *)

let ds1 = run_benchmark 
  ~filename:"last_index_of_page_single_fun_35" 
  ~input:page 
  ~ch:'%' 
  ~ctypes:[3;5]
  ~generators: page_gen

let ds2 = run_benchmark 
  ~filename:"last_index_of_page_single_fun_01246" 
  ~input:page 
  ~ch:'d' 
  ~ctypes:[0;1;2;4;6]
  ~generators: page_gen

let triple_to_string (a, b, c) =
  "(" ^ string_of_float a ^ ", " ^ string_of_float b ^ ", " ^ string_of_float c ^ ")"

let list_to_string_triple l =
  "[" ^ String.concat "; " (List.map triple_to_string l) ^ "]"
let list_to_string l =
  "[" ^ String.concat "; " (List.map string_of_float l) ^ "]"
let rec group3 = function
  | a :: b :: c :: rest -> (a, b, c) :: group3 rest
  | _ -> []

let convert ds = [List.nth ds 2; List.nth ds 3; List.nth ds 4; List.nth ds 0; List.nth ds 1; List.nth ds 6;List.nth ds 5]

let ds_group = convert (group3 (ds1 @ ds2))

let o_1 = [List.nth ds_group 0; List.nth ds_group 1; List.nth ds_group 2; List.nth ds_group 3]
let o_k = [List.nth ds_group 4; List.nth ds_group 5]
let o_n = [List.nth ds_group 6]
let group = [o_1; o_k; o_n]

let percent_one =  List.map avg_floats
[List.map (fun (x, y, z) -> x) o_1;  (List.map (fun (x, y, z) -> x) o_k); (List.map (fun (x, y, z) -> x) o_n)]

let percent_five =  List.map avg_floats
[List.map (fun (x, y, z) -> y) o_1;  (List.map (fun (x, y, z) -> y) o_k); (List.map (fun (x, y, z) -> y) o_n)]

let percent_ten =  List.map avg_floats
[List.map (fun (x, y, z) -> z) o_1;  (List.map (fun (x, y, z) -> z) o_k); (List.map (fun (x, y, z) -> z) o_n)]

let () = print_endline (list_to_string percent_one)
let () = print_endline (list_to_string percent_five)
let () = print_endline (list_to_string percent_ten)




let () = 
  let ds = ds1 @ ds2 in
  let ds_group = convert (group3 ds) in
  print_endline (list_to_string_triple ds_group)




(* let () = run_benchmark 
  ~filename:"last_index_of_page_3" 
  ~input:page 
  ~ch:'%' 
  ~ctypes:[3]
  ~generators: page_gen

let () = run_benchmark 
  ~filename:"last_index_of_page_0" 
  ~input:page 
  ~ch:'%' 
  ~ctypes:[0]
  ~generators: page_gen *)

(* let rhs = string_to_list (Base.read_file_to_string "./test/resources/stringOp/B.txt")

let () = match last_index_of rhs 'a' with
| Some k -> Printf.printf "%d" k
| None -> () *)