open Seq_change
open Pprinter
open Int_change
open Triple_change


module StringChange_1 = struct
  type t = string
  type dt = 
  | Noc
  | Ins of int * char
  | Del of int
  let noc = Noc
  let vc dt t = match dt with
  | Noc -> true
  | Ins (k, _) -> k >= 0 && k <= String.length t
  | Del k -> k >= 0 && k < String.length t

  let patch (ds : dt) (s : string) : string =
    let len = String.length s in
    match ds with
    | Noc -> s
    | Ins (k, c) ->
        if k < 0 || k > len then invalid_arg ("Ins: index out of bounds " ^ Int.to_string k ^ " " ^ s);
        let prefix = String.sub s 0 k in
        let suffix = String.sub s k (len - k) in
        prefix ^ String.make 1 c ^ suffix
    | Del k ->
        if k < 0 || k >= len then invalid_arg "Del: index out of bounds";
        let prefix = String.sub s 0 k in
        let suffix = String.sub s (k + 1) (len - k - 1) in
        prefix ^ suffix

  let v_to_string = function
  | "" -> "\"\""
  | x -> let buf = Buffer.create (String.length x) in
    String.iter (fun c ->
      if c = ' ' then
        Buffer.add_string buf "␣"
      else
        Buffer.add_char buf c
    ) x;
    "\"" ^ Buffer.contents buf ^ "\""
  let dv_to_string = function
  | Noc -> "String.Noc"
  | Ins (n, ' ') -> "Ins " ^ Int.to_string n ^ " " ^ "␣"
  | Ins (n, c) -> "Ins " ^ Int.to_string n ^ " " ^ String.make 1 c
  | Del n -> "Del " ^ Int.to_string n
end

module StringChange_2 = struct
  type t = string
  type dt = 
  | Prepend of char
  | Append of char

  let vc _ _ = true
  let patch (ds : dt) (s : t) : t = 
    match ds with
    | Prepend c -> String.make 1 c ^ s
    | Append c -> s ^ String.make 1 c
    let v_to_string x = x
  let dv_to_string = function
  | Prepend c -> "Prepend " ^  String.make 1 c
  | Append c -> "Append " ^ String.make 1 c
end

module DiffTrimLeft = struct
  open StringChange_1
  module CA = StringChange_1
  module CB = SeqChange(StringChange_1)
  module CS = struct
    type t = (int * bool) list
    type dt = CA.dt
    module P = SeqPrinter(PairPrinter(IntPrinter)(BoolPrinter))
    let prt = P.to_string 
    let rec patch_ins = function
    | [], _, ' ' -> [(1, true)]
    | [], _, _ -> [(1, false)]
    | (n, true) :: t, i, ' ' when i >= 0 && i < n ->
      (n + 1, true) :: t
    | (n, false) :: t, i, _ when i >= 0 && i < n ->
      (n + 1, false) :: t
    | (n, false) :: t, i, ' ' when i >= 0 && i < n ->
      (i, false) :: (1, true) :: (n - i, false) :: t
    | (n, true) :: t, i, _ when i >= 0 && i < n ->
      (i, true) :: (1, false) :: (n - i, true) :: t
    | (n, false) :: t, i, ' ' when i >= 0 && i < n ->
      (i, false) :: (1, true) :: (n - i, false) :: t
    | (n, b) :: t, i, c when n >=0 && i > n -> 
      (n, b) :: (patch_ins (t, i - n, c))
    | s, i, c -> invalid_arg ("Invalid state patch_ins" ^ prt s ^ CA.dv_to_string (Ins(i,c)))

    let rec patch_del = function
    | (n, b) :: t, i when i >= 0 && i < n && n > 0 ->
      (n - 1, b) :: t
    | (n, b) :: t, i when n > 0 && i >= n ->
      (n, b) :: patch_del (t, i)
    | s, i -> invalid_arg ("Invalid state" ^ prt s ^ CA.dv_to_string (Del i))

    let patch ds s = match ds with
    | Noc -> s
    | Ins(i, c) -> patch_ins (s, i, c)
    | Del i -> patch_del (s, i)

    let vc _ _ = true
    let v_to_string = prt
    let dv_to_string = CA.dv_to_string
  end
  let name = "trimLeft"

  let trim_left (s : string) : string =
    let len = String.length s in
    let rec find_first_non_space i =
        if i >= len then len
        else match s.[i] with
          | ' ' -> find_first_non_space (i + 1)
          | _ -> i
      in
      let start = find_first_non_space 0 in
      String.sub s start (len - start)
  let f = trim_left
  type st = (int * bool) list
  let repeat n x = List.init n (fun _ -> x)
  let dtrim_left (ds : dt) (s : st) : dt list = 
    match ds with
    | Noc -> []
    | Ins (i, c) -> begin
        match s with
          | [] -> if c = ' ' then [] else [Ins(i,c)]
          | (h, true) :: _ when 0 <= h && h <= i -> if c = ' ' then [] else [Ins (i - h, c)]
          | (h , true) :: _ when 0 <= h && i < h -> 
            if c = ' ' then [] else List.append (repeat (h - i) (Ins(0, ' '))) [Ins(0, c)]
          | (h, false) :: _ when 0 <= h && i = 0 && c = ' ' -> []
          | (h, false) :: _ when h >= 0 -> [Ins(i, c)]
          | _ -> invalid_arg ("Invalid state" ^ CA.dv_to_string ds)
       end
    | Del i -> begin
        match s with
        | (h, true) :: _ when 0 <= h && i < h -> []
        | (h, true) :: (1, false) :: (h', true) :: _ when 0 <= h && i = h -> repeat (h' + 1) (Del 0) 
        | (h, true) :: _ when 0 <= h && i >= h -> [Del(i - h)]
        | [(1, false)] when i = 0 -> [Del i]
        | (1, false) :: (h', true) :: _ when i = 0 -> repeat (h' + 1) (Del 0)
        | (h, false) :: _ when 0 <= h && 0 <= i -> [Del i]
          | _ -> invalid_arg ("Invalid state" ^ CA.dv_to_string ds)
        end
   
  let df = dtrim_left
  let init (s : string) : (int * bool) list =
    let len = String.length s in
    let rec aux i acc curr_len curr_kind =
      if i = len then
        if curr_len = 0 then List.rev acc
        else List.rev ((curr_len, curr_kind) :: acc)
      else
        let c = s.[i] in
        let is_space = c = ' ' || c = '\t' || c = '\n' || c = '\r' in
        match curr_len with
        | 0 -> aux (i + 1) acc 1 is_space
        | _ ->
            if is_space = curr_kind then
              aux (i + 1) acc (curr_len + 1) curr_kind
            else
              aux (i + 1) ((curr_len, curr_kind) :: acc) 1 is_space
    in
    aux 0 [] 0 false
end


module DiffIndexOf = functor (D : sig val pat : string end) -> struct
  open StringChange_1 
  open Kmp
  open D

  module CA = StringChange_1
  module CB = IntChange
  module CS = struct
    (* input and the index of the end of substring, if the substring does not exist, set index to -1 
    For example, ("abc", "ab")'s state is ("abc", 2),
                 ("abc", "d")'s state is ("abc", -1)
    
    Design choice: when the change to a string is before the last index, anything can happen, but changes after the last index won't influence the result. 
    *)
    type t = string * int 
    type dt = StringChange_1.dt
    let vc ds (s, i) = StringChange_1.vc ds s && (i == -1 || i >= String.length pat && i <= String.length s)
    let patch ds (s, i) = 
      (* assert (vc ds (s, i)); *)
      let f = StringChange_1.patch in
      let j = i - String.length pat in
      match ds with
      | Noc -> (s, i)
      | Ins(k, c) when k >= i -> (f ds s, i)
      | Ins(k, c) when k < i &&  not (String.contains pat c) -> (f ds s, i + 1)
      | Del k when k >= i -> (f ds s, i)
      | Del k when k < i && not (String.contains pat s.[k]) -> (f ds s, i - 1)
      | _ -> let s' = f ds s in match substr s' pat with -1 -> (s', -1) | m -> (s', m + j)

    let v_to_string (s, i) = "(" ^ s ^ ", " ^ Int.to_string i ^ ")"
    let dv_to_string = CA.dv_to_string
  end
  let name = "indexOf"

  let f s = substr s pat
  let dindex_of ds (s, i) = 
    assert (CS.vc ds (s, i));
    let patch = StringChange_1.patch in
    match ds with
    | Noc -> 0
    | Ins(k, c) when k >= i -> 0
    | Ins(k, c) when k <= i - String.length pat &&  not (String.contains pat c) -> 1
    | Del k when k >= i -> 0
    | Del k when k <= i - String.length pat && not (String.contains pat s.[k]) -> -1
    | _ -> let s' = patch ds s in match substr s' pat with -1 -> -(i - String.length pat) - 1 | m -> m - i

  let df = dindex_of

  let init s = 
    let i = substr s pat in
    if i = -1 then (s, -1) else (s, i + String.length pat)
end


module DiffSubString = struct
  module CA = TripleChange(StringChange_1)(IntChange)(IntChange)
  module CB = SeqChange(StringChange_1)
  module CS = struct
    type t = CA.t
    type dt = CA.dt
    let vc (ds, di, dj) (s, i, j) = 
      let (ii, jj) = (i + di, j + dj) in  
      StringChange_1.vc ds s && ii >= 0 && jj >= 0 && ii <= jj && jj <= String.length s
    let patch = CA.patch
    let v_to_string = CA.v_to_string
    let dv_to_string = CA.dv_to_string
  end

  open StringChange_1
  
  let f (s, i, j) = String.sub s i (j - i)
  
  let df_fst ds (s, i, j) = match ds with
  | Noc -> []
  | Ins(k, c) when k >= j -> []
  | Ins(k, c) when k < i -> [Ins (0, s.[i - 1]); Del (j - i)]
  | Ins(k, c) when k >= i && k < j -> [Ins(k-i, c); Del (j - i)]
  | Del k when k >= j -> []
  | Del k when k < i -> [Ins (j - i, s.[j]);Del 0]
  | Del k when k >= i && k < j -> [Ins (j - i, s.[j]); Del (k - i)]
  | _ -> invalid_arg "invalid change or state"
  
(*   aaaaa xxxx bbbbbbbbb  *)
(*    i = 5
      j = 9    
    ins 6 y 

    xxxx ~> xyxx
  *)


  let reverse_string s =
    let len = String.length s in
    String.init len (fun i -> s.[len - 1 - i])
  let rec string_as_change s k = 
    if String.length s = 0 then []
    else Ins(k, s.[0]) :: string_as_change (String.sub s 1 (String.length s - 1)) (k + 1)


  let df_snd di (s, i, j) = match di with
  | k when k > 0 -> List.init k (fun _ -> Del 0)
  | k when k < 0 -> string_as_change (String.sub s (i - k) k) 0
  | k when k = 0 -> []
  | _ -> invalid_arg ""

  let df_trd dj (s, i, j) = match dj with
  | k when k >= 0 -> string_as_change (String.sub s j k) (j - i)
  | k when k < 0 -> List.init k (fun _ -> Del (j - k))
  | k when k = 0 -> []
  | _ -> invalid_arg ""

  let df (ds, di, dj) (s, i, j) =
    let d1 = df_fst ds (s, i, j) in
    let d2 = df_snd di (StringChange_1.patch ds s, i, j) in
    let d3 = df_trd dj (StringChange_1.patch ds s, i + di, j) in
    List.concat [d1; d2; d3]
  let init x = x
  let name = "substring"
end