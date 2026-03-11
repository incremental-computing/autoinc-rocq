(* open Experiment
open Autoinc.String_op
open Rand

(* the change type of indexOf *)
let lio_ct = 
  [ "Deletion before the first occurence (best case)"
  ; "Deletion after the first occurence (best case)"
  ; "Insertion after the first occurence (best case)"
  ; "Deletion when the old result is None (best case)"
  ; "Insertion before the first occurence (intermediate case)"
  ; "Insertion when the old result is None (intermediate case)"
  ; "Deletion the first occurence (worst case)"
  ]

let change_generator_0 index _ = gen_del_at (0, index-1)

let change_generator_1 index s = gen_del_at (index+1, List.length s)
 
let change_generator_2 index s = gen_ins_at (index+1, List.length s)

let change_generator_3 s = gen_del_at (0, List.length s)  

let change_generator_4 index s = gen_ins_at (0, index-1)

let change_generator_5 s = gen_ins_at (0, List.length s)

let change_generator_6 index s size =
  let h = size / 2 in
    del (max (index - h) 0) (min (index + h) (List.length s))    

module type Generator = sig
  val generators : (int, char list -> int -> DString.dt) Hashtbl.t
end

module LastIndexOfSetup(C : Char)(G : Generator) = struct
  module OP = StringLastIndexOf(C)
  let change_cases = lio_ct
  let change_generator = G.generators

  let size = List.length
end

let paragraph = string_to_list (Base.read_file_to_string "./test/resources/lastIndexOf/paragraph.txt")
let page = string_to_list (Base.read_file_to_string "./test/resources/lastIndexOf/page.txt")

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
  let module A = Make(LastIndexOfSetup(C)(M)) in
  A.run_benchmark filename input ctypes [1; 5; 10] 5


let () = run_benchmark 
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
  ~generators: paragraph_gen

let () = run_benchmark 
  ~filename:"last_index_of_page_01246" 
  ~input:page 
  ~ch:'d' 
  ~ctypes:[0;1;2;4;6]
  ~generators: page_gen

let () = run_benchmark 
  ~filename:"last_index_of_page_35" 
  ~input:page 
  ~ch:'%' 
  ~ctypes:[3;5]
  ~generators: page_gen *)
