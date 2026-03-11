open Op
open Pair_change
open Bool_change
open Change
open Monoid

module type DiffOp = 
 sig
  type a
  type b
  type da
  type db
  val op : a -> b
  val dop : da -> db
end

module StatelessFunctor (M : StatelessDiffOp) = struct
  type a = M.CA.t
  type b = M.CB.t
  type da = M.CA.dt
  type db = M.CB.dt
  let op = M.f
  let dop = M.df
end

module StatefulFunctor(M : StatefulDiffOp) = struct
  type a = M.CA.t
  type b = M.CB.t
  type da = M.CA.dt
  type db = M.CB.dt
  let state : (M.CS.t option) ref = ref None
  let op x = state := Some (M.init x); M.f x
  let dop dx = 
    let st = !state in
    match st with
    | None -> failwith "Uninitialized state"
    | Some st -> 
      (* assert (M.CS.vc dx st); *)
      state := Some (M.CS.patch dx st);
      M.df dx st
end

module StatefulFunctorSingleFun(M : StatefulDiffOpSingleFun) = struct
  type a = M.CA.t
  type b = M.CB.t
  type da = M.CA.dt
  type db = M.CB.dt
  let state : (M.s option) ref = ref None
  let op x = state := Some (M.init x); M.f x
  let dop dx = 
    let st = !state in
    match st with
    | None -> failwith "Uninitialized state"
    | Some st -> 
      (* assert (M.CS.vc dx st); *)
      let (dy, st') = M.df dx st in
      state := Some st';
      dy
end

module Seq (F : DiffOp) (G : DiffOp with type db = F.da with type b = F.a) = struct
  type a = G.a
  type b = F.b
  type da = G.da
  type db = F.db
  let op x = F.op (G.op x)
  let dop da = F.dop (G.dop da)
end

module Pair (F : DiffOp) (G : DiffOp) 
            (H : DiffOp with type a = F.b * G.b with type da = (F.db, G.db) pair_change) = struct
  type a = F.a * G.a
  type b = H.b
  type da = (F.da, G.da) pair_change
  type db = H.db
  let op x = H.op (F.op (fst x), G.op (snd x))
  let dop = function
  | Pair_fst dx -> H.dop (Pair_fst (F.dop dx))
  | Pair_snd dy -> H.dop (Pair_snd (G.dop dy))
  | Pair_both (dx, dy) -> H.dop (Pair_both (F.dop dx, G.dop dy))  
end

module Triple (E : DiffOp) (F : DiffOp) (G : DiffOp) 
            (H : DiffOp with type a = E.b * F.b * G.b with type da = E.db * F.db * G.db) = struct
  type a = E.a * F.a * G.a
  type b = H.b
  type da = E.da * F.da * G.da
  type db = H.db
  let op (x, y, z) = H.op (E.op x, F.op y, G.op z)
  let dop (dx, dy, dz) = H.dop (E.dop dx, F.dop dy, G.dop dz)

end

module Lift (Op : DiffOp) = struct
  type a = Op.a
  type b = Op.b
  let op = Op.op
  type da = Op.da list
  type db = Op.db list
  let rec dop da = match da with
  | [] -> []
  | x :: xs -> Op.dop x :: dop xs
end

module type TYPE = 
 sig
  type ty
  type dty
  val noc: dty
end
module Lift_3_1 (A : TYPE) (B : TYPE) (C : TYPE)
    (Op : DiffOp with type a = A.ty * B.ty * C.ty with type da = A.dty * B.dty * C.dty) = struct
  type a = A.ty * B.ty * C.ty
  type b = Op.b
  type da = A.dty list * B.dty * C.dty
  type db = Op.db list
  let op = Op.op
  let dop (ass,b,c) = 
    let changes = (A.noc, b, c) :: List.map (fun a -> (a,B.noc,C.noc)) ass in
    List.map Op.dop changes
    (* let das = List.map (fun a -> (a,B.noc,C.noc)) ass in Op.dop das *)
end

module ID (C : Change) = struct
  type a = C.t
  type b = C.t
  type da = C.dt
  type db = C.dt
  let op = fun x -> x
  let dop = fun x -> x
end

(* module Const (C : Change) = struct
  type a = unit
  type b = C.t
  type da = unit
  type db = C.dt
  let op = fun x -> c
  let dop = fun x -> c
end *)
