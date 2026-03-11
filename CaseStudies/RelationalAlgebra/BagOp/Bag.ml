type 'a list =
| Nil
| Cons of 'a * 'a list

type 't bag = 't list
(* type 't bag = 't int hashmap *)

let rec find_bag_h k cmp l = 
  match l with
  | Nil -> k
  | Cons (x, l) -> if cmp x k then find_bag_h x cmp l else find_bag_h k cmp l
  
let bag_max = find_bag_h 0 (>)
let bag_min = find_bag_h max_int (<)

let rec bag_as_list = function 
| Nil -> []
| Cons (x, xs) -> x :: (bag_as_list xs)

(* bag diff *)
module MakeSetUtils (S : Set.S) = struct
  let of_list lst = List.fold_left (fun acc x -> S.add x acc) S.empty lst
  let print_set p = S.iter (fun x -> p x)
  let print_bag_diff p b1 b2 = 
    let (b1, b2) = (bag_as_list b1, bag_as_list b2) in 
    print_set p (S.diff (of_list b1) (of_list b2))
end
module HashMapDiff (Ord: Hashtbl.HashedType) = struct
  module H = Hashtbl

  (* Create a function to compute the difference between two hash maps *)
  let diff h1 h2 =
    let result = H.create (H.length h1) in
    H.iter (fun key value ->
      if not (H.mem h2 key) then
        H.add result key value
    ) h1;
    result
end

let list_to_hashtable lst =
  let tbl = Hashtbl.create (List.length lst) in
  List.iter (fun x ->
    let count = try Hashtbl.find tbl x with Not_found -> 0 in
    Hashtbl.replace tbl x (count + 1)
  ) lst;
  tbl

let bag_to_hashtable b = list_to_hashtable (bag_as_list b)


let bag_eq1 b1 b2 = (bag_to_hashtable b1) = (bag_to_hashtable b2)
let bag_eq2 b1 b2 = 
  let b1 = bag_as_list b1 in
  let b2 = bag_as_list b2 in
  let b1 = List.sort compare b1 in
  let b2 = List.sort compare b2 in
  b1 = b2
let rec bag_size b = 
  match b with
  | Nil -> 0
  | Cons (_, l) -> 1 + bag_size l

type 't bag_change =
| Bag_union of 't bag
| Bag_diff of 't bag

(* Print functions *)
let rec print_bag p = function 
| Nil -> ()
| Cons (e, Nil) -> p e
| Cons (e,l )-> p e ; print_string "; " ; print_bag p l

let string_of_bag p b = 
  let rec string_of_bag_helper = function
  | Nil -> ""
  | Cons (x, xs) -> p x ^ "; " ^ string_of_bag_helper xs
  in "[" ^ string_of_bag_helper b ^ "]"

let print_range_bag b =
  match b with
  | Nil -> Printf.printf "[]"
  | _ -> Printf.printf "%i .. %i" (bag_min b) (bag_max b)

let print_bag_change p c = match c with
| Bag_union b -> print_string "Bag_union ["; print_bag p b; print_string "]"
| Bag_diff b -> print_string "Bag_diff ["; print_bag p b; print_string "]"

let string_of_num_bag_change c = match c with
| Bag_union Nil -> "Bag_union []"
| Bag_union b -> "Bag_union (" ^ string_of_int (bag_min b) ^ " .. " ^ string_of_int (bag_max b) ^ ")" 
| Bag_diff Nil -> "Bag_diff []"
| Bag_diff b -> "Bag_diff (" ^ string_of_int (bag_min b) ^ " .. " ^ string_of_int (bag_max b) ^ ")"

let print_num_bag_change c = 
  let s = string_of_num_bag_change c in
  print_endline s


let bag_change_size = function
| Bag_union b -> bag_size b
| Bag_diff b -> bag_size b
let rec print_seq_change p cs = match cs with
| Nil -> ()
| Cons (c, Nil) -> p c
| Cons (c, cs) -> p c; print_string ", "; print_seq_change p cs

let print_pair p1 p2 x = print_string "("; p1 (fst x); print_string ", "; p2 (snd x); print_string ")"

(** val list_del : 'a1 eqDec -> 'a1 list -> 'a1 -> 'a1 list **)
let rec list_del eq l a =
  match l with
  | Nil -> Nil
  | Cons (hd, l0) ->
    (match eq hd a with
     | true -> l0
     | false -> Cons (hd, (list_del eq l0 a)))

(** val diff_bag : 'a1 eqDec -> 'a1 bag -> 'a1 bag -> 'a1 bag **)
let rec diff_bag eq x = function
| Nil -> x
| Cons (hd, tl) -> diff_bag eq (list_del eq x hd) tl



(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val id : __ -> __ **)

let id x =
  x


(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f0 = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f0 a), (map f0 t))

let rec flat_map f0 = function
| Nil -> Nil
| Cons (x, t) -> app (f0 x) (flat_map f0 t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f0 l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t) -> fold_left f0 t (f0 a0 b)


let bag_patch eq db b = match db with
  | Bag_union b0 -> app b b0
  | Bag_diff b0 -> diff_bag eq b b0



(* https://stackoverflow.com/questions/36681643/generating-list-of-integers-in-ocaml-without-recursion *)

let rec unfold_right f init =
    match f init with
    | None -> Nil
    | Some (x, next) -> Cons (x, unfold_right f next)

let range from upto =
  let irange x = if x > upto then None else Some (x, x + 1) in
  unfold_right irange from


let rec make_pair xs ys = match xs, ys with
| _, Nil -> Nil
| Nil, _ -> Nil
| Cons (x, xs), Cons (y, ys) -> Cons ((x, y), make_pair xs ys)