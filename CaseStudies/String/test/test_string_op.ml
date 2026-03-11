open Base
open Test_string_op_char
open Test_string_op_string
(* 
let () = print_endline "===trimLeft test==="
module A = Make(TestTrimLeft)
let () = A.run_tests ()

let () = print_endline "===indexOf test==="
module B = Make(TestIndexOf)
let () = B.run_tests ()

let () = print_endline "===substring test==="
module C = Make(TestSubstring)
let () = C.run_tests () *)

let () = print_endline "===lastIndexOf test==="
module C = Make(TestLastIndexOf)
let () = C.run_tests ()

let () = print_endline "===lastIndexOf test https==="
module D = Make(TestLastIndexOfHttps)
let () = D.run_tests ()