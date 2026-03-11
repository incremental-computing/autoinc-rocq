open BagOp.Bag

module type DiffOp = 
 sig
  type a
  type b
  val op : a -> b
  type da
  type db
  val dop : da -> db
end

module Seq (F : DiffOp) (G : DiffOp with type db = F.da with type b = F.a) = struct
  type a = G.a
  type b = F.b
  let op a = F.op (G.op a)
  type da = G.da
  type db = F.db
  let dop da = F.dop (G.dop da)
end


open BagOp.Pair

module Bin (F : DiffOp) (G : DiffOp) (H : DiffOp with type da = (F.db, G.db) pair_change with type a = F.b * G.b) = struct
  type a = F.a * G.a
  type b = H.b
  let op a = H.op (F.op (fst a), G.op (snd a))
  type da = (F.da, G.da) pair_change
  type db = H.db
  let dop da = match da with
  | Pair_fst da1 -> H.dop (Pair_fst (F.dop da1))
  | Pair_snd da2 -> H.dop (Pair_snd (G.dop da2))
  | Pair_both (da1, da2) -> H.dop (Pair_both (F.dop da1, G.dop da2))
end

module Lift (Op : DiffOp) = struct
  type a = Op.a
  type b = Op.b
  let op = Op.op
  type da = Op.da bag
  type db = Op.db bag
  let rec dop da = match da with
  | Nil -> Nil
  | Cons (x, xs) -> Cons (Op.dop x, dop xs)
end

let timed (f : unit -> 'a) : 'a * float =
  Gc.full_major();
  let start = Sys.time () in
  let result = f () in
  let finish = Sys.time () in
  (result, finish -. start)