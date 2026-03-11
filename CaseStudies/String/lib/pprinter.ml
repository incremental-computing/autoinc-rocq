module type PPrinter = sig
  type t
  val to_string : t -> string
end

module PairPrinter (P_fst : PPrinter) (P_snd : PPrinter) = struct
  type t = P_fst.t * P_snd.t
  let to_string x = 
    let (x, y) = x in 
    "(" ^ P_fst.to_string x ^ ", " ^  P_snd.to_string y ^ ")"
end

module SeqPrinter (P : PPrinter) = struct
  type t = P.t list
  let to_string x =   
    let rec f = function
    | [] -> ""
    | [c] -> P.to_string c
    | c :: cs -> P.to_string c ^ ", " ^ f cs in
    "[" ^ (f x) ^ "]"
end

module IntPrinter = struct
  type t = int
  let to_string = Int.to_string 
end

module BoolPrinter = struct
  type t = bool
  let to_string = Bool.to_string 
end

module CharPrinter = struct
  type t = char
  let to_string = String.make 1 
end