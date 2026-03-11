open Change
open Pprinter

module SeqChange (C : Change) = struct
  type t = C.t
  type dt = C.dt list
  let rec vc dxs x = match dxs with
  | [] -> true
  | dx :: dxs -> C.vc dx x && vc dxs (C.patch dx x)
  let rec patch dxs x = match dxs with
  | [] -> x
  | dx :: dxs -> patch dxs (C.patch dx x) 
  let v_to_string = C.v_to_string
  let dv_to_string x =   
    let rec f = function
    | [] -> ""
    | [c] -> C.dv_to_string c
    | c :: cs -> C.dv_to_string c ^ ", " ^ f cs in
    "[" ^ (f x) ^ "]"
end

