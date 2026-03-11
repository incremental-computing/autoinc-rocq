(* This file is used to generate random insertion and deletion changes *)

open Autoinc.String_op

(* generate a random number that >= lower and <= upper *)
let random_int lower upper =
  lower + Random.int (upper - lower + 1)

let random_readable_string len =
  let words = [|
    "hello"; "world"; "example"; "ocaml"; "language"; "random"; "value"; "function";
    "simple"; "test"; "data"; "number"; "string"; "code"; "logic"; "comma"; "dot";
    "generate"; "fun"; "good"; "nice"; "fast"; "cool"; "small"; "big"; "easy"; "hard"
  |] in
  let punctuation = [| "."; "," |] in
  let buffer = Buffer.create len in
  let rec add_words n first =
    if n <= 0 then ()
    else
      let word = words.(Random.int (Array.length words)) in
      let word = if first then String.capitalize_ascii word else word in
      Buffer.add_string buffer word;
      if n > 1 then
        let punct =
          if Random.int 8 = 0 then Some punctuation.(Random.int 2) else None
        in
        (match punct with
         | Some p -> Buffer.add_string buffer (p ^ " ")
         | None -> Buffer.add_char buffer ' ')
      else
        Buffer.add_char buffer '.';
      add_words (n - 1) false
  in
  let avg_word_len = 5 in
  let estimated_words = max 1 (len / (avg_word_len + 1)) in
  add_words estimated_words true;
  let result = Buffer.contents buffer in
  if String.length result > len then String.sub result 0 len else result


(*
gen_ins_at 
input: 
- lower, upper: interval of the insertion position
- size: the size of inserted string
output: an insertion change between the interval
*)

let gen_ins_at (lower, upper) size = 
  let pos = random_int lower upper in
  let substr = random_readable_string size in
  ins pos substr

(*
gen_del_at
input: 
- lower, upper: interval of the insertion position
- size: the size of inserted string
output: an deletion change between the interval
*)

let gen_del_at (lo, hi) size =
  if size > hi - lo + 1 then
    del lo hi
  else
    let start = lo + Random.int (hi - lo + 1 - size) in
    del start size
