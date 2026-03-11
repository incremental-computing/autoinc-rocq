(* Changes for integers *)
type int_change = 
| Shift of int

let patch_int_change c x = 
  match c with Shift x' -> x + x'

module DiffInt = struct
  type delta_E = int_change
  let diff x y = Shift (y - x)
end

(** print_int_change : int_change -> unit *)
let string_of_int_change c = match c with
 Shift b -> "Shift " ^ string_of_int b 
let print_int_change c = match c with
| Shift b -> print_endline (string_of_int_change c)

