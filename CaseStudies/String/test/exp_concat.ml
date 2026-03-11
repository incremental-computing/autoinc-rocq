open Diffop_experiment
open Autoinc.String_op
open Autoinc.Opbase
open Autoinc.Op
open Autoinc.Pair_change
open Autoinc.Seq_change

module Concat = StatefulFunctor(StringConcat)


let lhs = string_to_list "A short history The algorithms that we examine have an interesting history; we summarize it here to help place the various methods io perspective."
let rhs = string_to_list "There is a simple brute-force algorithm for substring search that is in widespread use. While it has a worst-case running time proportional to MN, the strings that arise in many applications lead to a running time that is (except in pathological cases) proportional to M  N. Furthermore, it is well-suited to standard architectural features on most computer systems, so an optimized version provides a standard benchmark that is difficult to beat, even with a clever algorithm."



let cases = [
  "Doing deletion change to lhs - O(1)"
; "Inserting k characters to lhs - O(k) "
; "Doing lastIndexOf's O(1) deletion change to rhs - O(k)"
; "Doing lastIndexOf's O(k) insertion change of size k to rhs - O(2*k)"
; "Deleting the last occurrence of 'A' in rhs - O(|lhs| + |rhs|)"
]

let len = List.length

(* Doing deletion change to lhs - O(1) *)
let generator_0 (lhs, rhs) size = Pair_fst (ins 10 "0")


let non_param_generator = [
  (0, generator_0)
]


let generators = hashtbl_of_list (non_param_generator)

module StringOpSetUp = struct
  module OP = Concat
  let change_cases = cases
  let change_generator = generators
  let size (a, b) = (List.length a + List.length b)
end


let run_benchmark ~filename ~input ~ctypes ~generators = 
  let module A = Make(StringOpSetUp)(PairChange(DString)(DString))(SeqChange(DString)) in
  A.run_benchmark filename input ctypes [1;5;10] 100

let ds = run_benchmark 
  ~filename:"string_concat" 
  ~input:(lhs, rhs) 
  ~ctypes:[0]
  ~generators: generators
