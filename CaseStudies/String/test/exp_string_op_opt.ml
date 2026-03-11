open Diffop_experiment
open Autoinc.String_op
open Autoinc.Opbase
open Autoinc.Op
open Autoinc.Pair_change
open Autoinc.Seq_change
open Rand

module ToLowerCase = StatelessFunctor(StringToLowerCase)
module ToUpperCase = StatelessFunctor(StringToUpperCase)
module Concat = StatefulFunctor(StringConcat)

module A = Pair(ToLowerCase)(ToUpperCase)(Concat)
module LastIndexOf_A = 
StatefulFunctorSingleFun(StringLastIndexOfSingleFun(struct let c = 'A' end))

module B = Seq(Lift(LastIndexOf_A))(A)


let lhs = string_to_list (Base.read_file_to_string "./test/resources/stringOp/A.txt")
let rhs = string_to_list (Base.read_file_to_string "./test/resources/stringOp/B.txt")


let cases = [
  "Doing deletion change to lhs - O(1)"
; "Inserting k characters to lhs - O(k) "
; "Doing lastIndexOf's O(1) deletion change to rhs - O(k)"
; "Doing lastIndexOf's O(k) insertion change of size k to rhs - O(2*k)"
; "Deleting the last occurrence of 'A' in rhs - O(|lhs| + |rhs|)"
]

let len = List.length

(* Doing deletion change to lhs - O(1) *)
let generator_0 (lhs, rhs) size = Pair_fst (gen_del_at (0, len lhs) size)

(* Inserting k characters to lhs - O(k) *)
let generator_1 (lhs, rhs) size = Pair_fst (gen_ins_at (0, len lhs) size)

(* Doing lastIndexOf's O(1) deletion change to rhs - O(1) *)
let generator_2 index (lhs, rhs) size = Pair_snd (gen_del_at (0, index) size)


(* Doing lastIndexOf's O(k) insertion change of size k to rhs - O(2*k) *)
let generator_3 index (lhs, rhs) size = Pair_snd (gen_ins_at (index + 1, len rhs) size) 

(* Deleting the last occurrence of 'A' in rhs - O(|lhs| + |rhs|)*)
(* let generator_4 index (lhs, rhs) size = Pair_snd (gen_del_at (index + 1, len rhs) size)  *)
let generator_4 index (lhs, rhs) size =
  let h = size / 2 in
    Pair_snd (del (max (index - h) 0) (min (index + h) (len rhs)))


let param_generator k = [
  (2, generator_2 k)
; (3, generator_3 k)
; (4, generator_4 k)
]

let non_param_generator = [
  (0, generator_0)
; (1, generator_1)
]


let generators = hashtbl_of_list (param_generator 563 @ non_param_generator)

module StringOpSetUp = struct
  module OP = B
  let change_cases = cases
  let change_generator = generators
  let size (a, b) = (List.length a + List.length b)
end


let run_benchmark ~filename ~input ~ctypes ~generators = 
  let module A = Make(StringOpSetUp)(PairChange(DString)(DString))(SeqChange(DOption(DNat))) in
  A.run_benchmark filename input ctypes [1;5;10] 3000

let ds = run_benchmark 
  ~filename:"string_op_exp_opt" 
  ~input:(lhs, rhs) 
  ~ctypes:[0;1;2;3;4]
  ~generators: generators

let rec group3 = function
  | a :: b :: c :: rest -> (a, b, c) :: group3 rest
  | _ -> []

let ds_group = group3 ds


let percent_one = List.map (fun (x, y, z) -> x) ds_group 
let percent_five = List.map (fun (x, y, z) -> y) ds_group 
let percent_ten = List.map (fun (x, y, z) -> z) ds_group 


let list_to_string l =
  "[" ^ String.concat "; " (List.map string_of_float l) ^ "]"
let () = print_endline (list_to_string percent_one)
let () = print_endline (list_to_string percent_five)
let () = print_endline (list_to_string percent_ten)

  

(* let () = run_benchmark 
  ~filename:"string_op_exp_1" 
  ~input:(lhs, rhs) 
  ~ctypes:[1]
  ~generators: generators *)



(* let () = Printf.printf "%d" (List.length lhs) *)
  
(* let () = match B.op (lhs, rhs) with
| Some k -> Printf.printf "%d" k
| None -> ()



let make_char (ch : char) : (module Char) = 
  let module C = struct
    let c = ch
  end in
  (module C : Char)

let make_lastIndexOf (ch : char) : (module DiffOp) = 
  let (module C) = make_char (ch) in
  (module StatefulFunctor(StringLastIndexOf(C))) *)
