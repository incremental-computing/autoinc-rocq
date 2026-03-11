open Pair_change
open Seq_change

type nat = 
| O 
| S of nat

let rec nat_of_int x = 
  match x with
  | O -> 0
  | S n -> 1 + nat_of_int n

let rec int_of_nat x =
  assert (x >= 0);
  if x = 0 then
    O
  else
    S (int_of_nat (x - 1))
    
module PPrinter = struct
  type t = nat
  let to_string x = string_of_int (nat_of_int x)
end

type dnat = 
| Add of nat
| Sub of nat

module ChangePPrintter = struct
  type t = dnat
  let to_string = function
  | Add n -> "Add " ^ PPrinter.to_string n
  | Sub n -> "Sub " ^ PPrinter.to_string n
end

let rec nat_plus x y = 
  match x with
  | O -> y
  | S x -> S (nat_plus x y)

let rec nat_minus x y =
  match x, y with
  | O, _ -> O
  | _, O -> x
  | S x, S y -> (nat_minus x y) 

let rec nat_times x y =
  match x with
  | O -> O
  | S x -> nat_plus y (nat_times x y)

let rec nat_eq x y = 
  match x, y with
  | O, O -> true
  | S _, O -> false
  | O, S _ -> false
  | S x, S y -> nat_eq x y

let rec nat_lt x y =
  match x, y with
  | O, O -> false
  | O, S _ -> true
  | S _, O -> false
  | S x, S y -> nat_lt x y

module NatChange = struct
  type t = nat
  type dt = dnat
  let vc dx x = match dx with
  | Add _ -> true
  | Sub n -> nat_eq n x || nat_lt n x
  let patch dx x = assert (vc dx x); match dx with
  | Add n -> nat_plus x n
  | Sub n -> nat_minus x n
  let v_to_string x = string_of_int (nat_of_int x)
  let dv_to_string = function
  | Add n -> "Add " ^ PPrinter.to_string n
  | Sub n -> "Sub " ^ PPrinter.to_string n
end

module DiffIncOne = struct
  module CA = NatChange
  module CB = NatChange
  let f (x : nat) = S x
  let df (dx : dnat) = dx
end

module DiffTimes = struct
  module CA = PairChange(NatChange)(NatChange)
  module CB = SeqChange(NatChange)
  module CS = PairChange(NatChange)(NatChange)
  let f x = nat_times (fst x) (snd x)
  let dnat_nat_times x = function
  | Add n -> Add (nat_times x n)
  | Sub n -> Sub (nat_times x n)

  let dnat_dnat_times dx dy = match dx, dy with
  | Add x, Add y -> Add (nat_times x y)
  | Sub x, Sub y -> Add (nat_times x y)
  | Add x, Sub y -> Sub (nat_times x y)
  | Sub x, Add y -> Sub (nat_times x y)
  let df dxy st = assert (CS.vc dxy st); match dxy with
  | Pair_fst dx -> [dnat_nat_times (snd st) dx]
  | Pair_snd dy -> [dnat_nat_times (fst st) dy]
  | Pair_both (dx, dy) -> [dnat_nat_times (snd st) dx; dnat_nat_times (fst st) dy; dnat_dnat_times dx dy]
  let init x = x
end

