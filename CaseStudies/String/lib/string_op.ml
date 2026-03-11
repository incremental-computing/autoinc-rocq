open Pprinter
open Pair_change
open Seq_change
open Change
open Op

(* stateful string operators 

- isEmpty
- concat
- lastIndexOf

*)


(** val app : 'a1 list -> 'a1 list -> 'a1 list **)


(* type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool *)

(** val add : nat -> nat -> nat **)



module DNat =
 struct
  type dt =
  | Add of int
  | Sub of int
    (** val _UU0394_Nat : (nat, _UU0394_nat) change **)
  type t = int
  let patch dt t =
    match dt with
    | Add m -> t + m
    | Sub m -> t - m
  let vc dx x = x >= 0 && match dx with
  | Add n -> n >= 0 
  | Sub n -> n >= 0 && n <= x
  let v_to_string = Int.to_string
  let dv_to_string = function
  | Add n -> "Add " ^ v_to_string n
  | Sub n -> "Sub " ^ v_to_string n
 end

module DString =
 struct
  type t = char list
  type dt =
  | Noc
  | Ins of int * char list
  | Del of int * int

  (** val patch_ins : nat -> ascii list -> ascii list -> ascii list **)

  let rec patch_ins i s s' = 
    if i = 0 then
       s' @ s
    else
      (match s with
       | [] -> s'
       | x :: s0 -> x :: (patch_ins (i - 1) s0 s'))

  (** val patch_del : ascii list -> nat -> nat -> ascii list **)

  let rec patch_del s i n =
    match s with
    | [] -> []
    | x :: xs when i = 0 -> 
      if n = 0 then x :: xs else patch_del xs 0 (n - 1)
    | x :: xs -> 
      if n = 0 then x :: xs else x :: patch_del xs (i - 1) n



  (** val patch : _UU0394_str -> ascii list -> ascii list **)

  let patch ds s =
    match ds with
    | Noc -> s
    | Ins (i, s') -> patch_ins i s s'
    | Del (i, n) -> patch_del s i n
  let vc ds s = 
    match ds with
    | Noc -> true
    | Ins (i, s') -> i < (List.length s)
    | Del (i, n) -> (i + n) < (List.length s)

  let char_list_to_string (lst : char list) : string =
    let len =
      let rec count acc = function
        | [] -> acc
        | _ :: xs -> count (acc + 1) xs
      in
      count 0 lst
    in
    let bytes = Bytes.create len in
    let rec fill i = function
      | [] -> ()
      | c :: xs -> Bytes.set bytes i c; fill (i + 1) xs
    in
    fill 0 lst;
    Bytes.unsafe_to_string bytes
  let pprint = function
    | "" -> "\"\""
    | x -> let buf = Buffer.create (String.length x) in
      String.iter (fun c ->
        if c = ' ' then
          Buffer.add_string buf "␣"
        else
          Buffer.add_char buf c
      ) x;
      "\"" ^ Buffer.contents buf ^ "\""
  let v_to_string (s : t) = pprint (char_list_to_string s) 
  let dv_to_string = function
  | Noc -> "String.Noc"
  | Ins (n, s) -> "Ins " ^ DNat.v_to_string n ^ " " ^ (v_to_string s)
  | Del (i, n) -> "Del " ^ DNat.v_to_string i ^ " " ^ DNat.v_to_string n
 end

module StringLength =
 struct
  let f = List.length
  let df = function
  | DString.Noc -> DNat.Add 0
  | DString.Ins (_, s) -> DNat.Add (List.length s)
  | Del (_, n) -> DNat.Sub n
 end

module DBool =
 struct
  type t = bool
  type dt = 
  | Noc
  | Neg 
  
  let vc (_ : dt) (_ : t) = true
  let patch dt t = match dt with Noc -> t | Neg -> Bool.not t
  let v_to_string t = Bool.to_string t
  let dv_to_string = function
  | Noc -> "Noc"
  | Neg -> "Neg"
 end

module StringIsEmpty =
 struct
  module CA = DString
  module CB = DBool
  module CS = struct
    type t = int
    type dt = CA.dt
    let patch dt t =
      match dt with
      | DString.Noc -> t
      | DString.Ins (_, s) -> t + (List.length s)
      | DString.Del (_, n) -> t - n
    let vc dt t = 
      match dt with
      | DString.Noc -> true
      | DString.Ins (i, _) -> i <= (List.length t)
      | DString.Del (i, n) -> (i + n) <= (List.length t)
    let v_to_string = DNat.v_to_string
    let dv_to_string = DString.dv_to_string
  end

  (** val f : coq_A -> bool **)

  let f = function
  | [] -> true
  | _ -> false

  (** val df : dA -> coq_ST -> dB **)

  let df ds st =
    match ds with
    | DString.Noc -> DBool.Noc
    | DString.Ins (_, s) when st = 0 -> 
      (match s with
      | [] -> DBool.Noc
      | _ -> DBool.Neg)
    | DString.Ins (_, s) -> DBool.Noc
    | DString.Del (_, n) ->
      if st = 0 then DBool.Noc else if n < st then DBool.Noc else DBool.Neg
 end



module StringConcat =
 struct
  module CA = PairChange(DString)(DString)
  module CB = SeqChange(DString)

  module CS = struct
    type t = int
    type dt = CA.dt
    let patch_helper = function
    | DString.Noc -> DNat.Add 0
    | DString.Ins (_, s) ->
      DNat.Add (List.length s)
    | DString.Del (_, n) -> DNat.Sub n

    let patch dt t = 
      match dt with
      | Pair_fst dx -> DNat.patch (patch_helper dx) t
      | Pair_snd dx -> t
      | Pair_both (dx, dy) -> DNat.patch (patch_helper dx) t
    let vc dt t = true 
      (* match dt with
      | Pair_fst dx -> StringIsEmpty.CS.vc dx t
      | Pair_snd dx -> true
      | Pair_both (dx, dy) -> StringIsEmpty.CS.vc dx t *)
    let v_to_string = Int.to_string
    let dv_to_string = CA.dv_to_string
  end


  let f s =
    (fst s) @ (snd s)


  let shift ds n =
    match ds with
    | DString.Noc -> DString.Noc
    | DString.Ins (i, s) ->
      DString.Ins ((i + n), s)
    | DString.Del (i, k) ->
      DString.Del ((i + n), k)

  let df (s : CA.dt) (st : CS.t) =
    match s with
    | Pair_fst dx -> [dx]
    | Pair_snd dx -> [shift dx st]
    | Pair_both (dx, dy) -> [shift dy st; dx]
  let init (s1, s2) = List.length s1
 end

 module type Char =
 sig
  val c : char
 end

module DOption(C : Change) =
 struct
  type t = C.t option
  type dt =
  | Noc
  | To_some of C.t
  | As_some of C.dt
  | To_none

  let patch dt (t : t) = 
    match dt with
    | Noc -> t
    | To_some k -> Some k
    | As_some dt -> begin match t with None -> None | Some t -> Some (C.patch dt t) end
    | To_none -> None

  let vc dt t = 
    match dt, t with
    | Noc, _ -> true
    | To_some _, None -> true
    | As_some dt, Some t -> C.vc dt t
    | To_none, Some _ -> true 
    | _, _ -> false

  let v_to_string v = 
    match v with
    | None -> "None"
    | Some v -> "Some " ^ C.v_to_string v
  let dv_to_string dv = 
    match dv with
    | Noc -> "Noc"
    | To_some v -> "To_some(" ^ C.v_to_string v ^ ")"
    | As_some dv -> "As_some(" ^ C.dv_to_string dv ^ ")"
    | To_none -> "To_none"
 end

(** val last_index_of_helper :
    ascii list -> ascii -> nat -> nat option -> nat option **)

let rec last_index_of_helper s c0 i res =
  match s with
  | [] -> res
  | x :: xs ->
    if x = c0 then 
      last_index_of_helper xs c0 (i + 1) (Some i)
    else
      last_index_of_helper xs c0 (i + 1) res

(** val last_index_of : ascii list -> ascii -> nat option **)

let last_index_of s c0 =
  last_index_of_helper s c0 0 None

type ('t, 'x) difference =
  't -> 't -> 'x
  (* singleton inductive, whose constructor was Build_Difference *)


(** val natDiff : (nat, DNat._UU0394_nat) difference **)

let natDiff x y =
  match x < y with
  | true -> DNat.Add (y - x)
  | false -> DNat.Sub (x - y)

(** val last_index_of_helper :
    ascii list -> ascii -> nat -> nat option -> nat option **)

let rec last_index_of_helper s c0 i res =
  match s with
  | [] -> res
  | (x :: xs) ->
    if x = c0 then
      last_index_of_helper xs c0 (i + 1) (Some i)
    else
      last_index_of_helper xs c0 (i + 1) res

(** val last_index_of : ascii list -> ascii -> nat option **)

let last_index_of s c0 =
  last_index_of_helper s c0 0 None


module StringLastIndexOfSingleFun =
 functor (C:Char) ->
 struct
  module CA = DString
  module CB = DOption(DNat)
  type s = CA.t * CA.dt list * CB.t

  let f s = last_index_of s C.c
  let init x = (x, [], f x)

  let rec patch_reverse dxs input = 
    match dxs with
    | [] -> input
    | dx :: rest ->
      let r = patch_reverse rest input in
      CA.patch dx r

  let df dx (input, changes, output) =
    (* let x' = CA.patch dx input in *)
    let res = (match dx with
     | DString.Noc -> (CB.Noc, (input, changes, output))
     | DString.Ins (i, s0) ->
       (match output with
        | Some k ->
          (match k < i with
           | true ->
             (match last_index_of s0 C.c with
              | Some j ->
                let newOut = j + i in
                let dy = CB.As_some (DNat.Add (newOut - k)) in 
                (dy, (input, dx :: changes, Some (newOut)))
              | None -> (CB.Noc, (input, dx :: changes, output))
            )
           | false ->
             let len = List.length s0 in
             let dy = CB.As_some (DNat.Add len) in 
              (dy, (input, dx :: changes, Some (k + len))))
        | None ->
          (match last_index_of s0 C.c with
           | Some k -> 
              let out = k + i in
              let dy = CB.To_some (out) in
              (dy, (input, dx :: changes, Some out))
           | None -> (CB.Noc, (input, dx :: changes, output))))
     | DString.Del (i, n) ->
       (match output with
        | Some k ->
          (match i + n < k with
           | true -> 
              let dy = CB.As_some (DNat.Sub n) in
              (dy, (input, dx :: changes, Some(k - n)))
           | false ->
             (match k < i with
              | true -> (CB.Noc, (input, dx :: changes, output))
              | false -> 
                let updated_input = patch_reverse (dx :: changes) input in
                let updated_output = last_index_of updated_input C.c in
                (match updated_output with
                 | Some j -> 
                    let dy = CB.As_some (natDiff k j) in
                    (dy, (updated_input, [], Some j))
                 | None -> 
                  (CB.To_none, (updated_input, [], None))
                )))
        | None -> (CB.Noc, (input, dx :: changes, output) ) )) in

      (* let () = print_endline ("Using LastIndexSingleFun with char: " ^ String.make 1 C.c) in *)
      res
end


module StringLastIndexOf =
 functor (C:Char) ->
 struct
  module CA = DString
  module CB = DOption(DNat)
  module CS = struct
    type t  = CA.t * CB.t
    type dt = CA.dt
    let patch dx (input, output) = 
      let new_input = DString.patch dx input in
      (match dx with
      | DString.Noc -> (new_input, output)
      | DString.Ins (i, s) ->
        (match output with
          | Some k ->
            (match k < i with
            | true ->
              (match last_index_of s C.c with
                | Some j ->  (new_input, (Some (j + i)))
                | None ->  (new_input, (Some k)))
            | false ->  (new_input, (Some (k + (List.length s)))))
          | None ->
            (match last_index_of s C.c with
            | Some k ->  (new_input, (Some (k + i)))
            | None -> (new_input, None)))
      | DString.Del (i, n) ->
        (match output with
          | Some k ->
            (match (i + n) < k with
            | true ->  (new_input, (Some (k - n)))
            | false ->
              (match k < i with
                | true ->  (new_input, (Some k))
                | false ->  (new_input, (last_index_of new_input C.c))))
          | None ->  (new_input, None)))
    let vc dx x = let (input, output) = x in CA.vc dx input
    let v_to_string (input, output) = "(" ^ DString.v_to_string input ^ ", " ^ CB.v_to_string output ^ ")"
    let dv_to_string = CA.dv_to_string
  end



  let f s = last_index_of s C.c

  (** val _UU0394_f : _UU0394_A -> coq_ST -> _UU0394_B **)

  let df dx (input, output) =
    (match dx with
     | DString.Noc -> CB.Noc
     | DString.Ins (i, s0) ->
       (match output with
        | Some k ->
          (match k < i with
           | true ->
             (match last_index_of s0 C.c with
              | Some j ->
                CB.As_some (DNat.Add
                  (j + i - k))
              | None -> CB.Noc)
           | false ->
             CB.As_some (DNat.Add
               (List.length s0)))
        | None ->
          (match last_index_of s0 C.c with
           | Some k -> CB.To_some (k + i)
           | None -> CB.Noc))
     | DString.Del (i, n) ->
       (match output with
        | Some k ->
          (match i + n < k with
           | true -> CB.As_some (DNat.Sub n)
           | false ->
             (match k < i with
              | true -> CB.Noc
              | false -> 
                let updated_input = 
                  last_index_of (DString.patch dx input) C.c in
                (match updated_input with
                 | Some j -> CB.As_some (natDiff k j)
                 | None -> CB.To_none)))
        | None -> CB.Noc))

  let init x = (x, f x)
 end


(** val index_of_helper : ascii list -> ascii -> nat -> nat option **)

let rec index_of_helper s c0 i =
  match s with
  | [] -> None
  | x :: xs ->
    (match x = c0 with
     | true -> Some i
     | false -> index_of_helper xs c0 (i + 1))

(** val index_of : ascii list -> ascii -> nat option **)

let index_of s c0 =
  index_of_helper s c0 0

module StringIndexOf = functor (C:Char) ->
 struct
  module CA = DString
  module CB = DOption(DNat)
  module CS = struct
    type t = CA.t * CB.t
    type dt = CA.dt
    let patch dx (input, output) = 
      let new_input = DString.patch dx input in
      (match dx with
        | DString.Noc -> (input, output)
        | DString.Ins (i, s) ->
          (match output with
            | Some j ->
              (match j < i with
              | true -> (new_input, (Some j))
              | false ->
                (match index_of s C.c with
                  | Some k -> (new_input, (Some (i + k)))
                  | None -> (new_input, (Some (j + (List.length s))))))
            | None ->
              (match index_of s C.c with
              | Some j -> (new_input, Some (i + j))
              | None -> (new_input, None)))
        | DString.Del (i, n) ->
          (match output with
            | Some j ->
              (match j < i with
              | true -> (new_input, (Some j))
              | false ->
                (match i + n < j with
                  | true -> (new_input, (Some (j - n)))
                  | false -> (new_input, (index_of new_input C.c))))
            | None -> (new_input, None)))
    let vc _ _ = true
  end
  

  let f = index_of
  let df dx (input, output) = 
    (match dx with
     | DString.Noc -> CB.Noc
     | DString.Ins (i, s) ->
       (match output with
        | Some k ->
          (match k < i with
           | true -> CB.Noc
           | false ->
             (match index_of s C.c with
              | Some n -> CB.As_some (natDiff k (i + n))
              | None ->
                CB.As_some (DNat.Add
                  (List.length s))))
        | None ->
          (match index_of s C.c with
           | Some n -> CB.To_some (n + i)
           | None -> CB.Noc))
     | DString.Del (i, n) ->
       (match output with
        | Some k ->
          (match k < i with
           | true -> CB.Noc
           | false ->
             (match i + n < k with
              | true ->
                CB.As_some (DNat.Sub n)
              | false ->
                (match index_of
                         (DString.patch dx input)
                         C.c with
                 | Some j -> CB.As_some (natDiff k j)
                 | None -> CB.To_none)))
        | None -> CB.Noc))
  let init x = (x, f x)
end


let string_to_list (s : string) : char list =
  let rec aux i =
    if i < 0 then []
    else s.[i] :: aux (i - 1)
  in
  let rec reverse acc = function
    | [] -> acc
    | x :: xs -> reverse (x :: acc) xs
  in
  reverse [] (aux (String.length s - 1))

let ins x s = DString.Ins(x, string_to_list s)
let del i n = DString.Del(i, n)


module StringToLowerCase =
 struct
  module CA = DString
  module CB = DString
  let f = List.map Char.lowercase_ascii
  let df = function
  | DString.Noc -> DString.Noc
  | DString.Ins(i, s) -> DString.Ins (i, f s)
  | DString.Del(i, n) -> DString.Del (i, n)
 end 

module StringToUpperCase =
 struct
  module CA = DString
  module CB = DString
  let f = List.map Char.uppercase_ascii
  let df = function
  | DString.Noc -> DString.Noc
  | DString.Ins(i, s) -> DString.Ins (i, f s)
  | DString.Del(i, n) -> DString.Del (i, n)
 end 
