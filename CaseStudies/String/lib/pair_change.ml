open Change
open Pprinter

type ('da, 'db) pair_change =
| Pair_fst of 'da
| Pair_snd of 'db
| Pair_both of 'da * 'db


module ChangePPrintter(P_fst : PPrinter) (P_snd : PPrinter) = struct
  type t = (P_fst.t, P_snd.t) pair_change
  let to_string = function    
  | Pair_fst da -> "Pair_fst (" ^ P_fst.to_string da ^ ")"
  | Pair_snd db -> "Pair_snd (" ^ P_snd.to_string db ^ ")"
  | Pair_both (da, db) -> 
    "Pair_both (" ^ P_fst.to_string da ^ ", " ^ P_snd.to_string db ^ ")"
end

module PairChange (CA : Change) (CB : Change) = struct
  type t = CA.t * CB.t
  type dt = (CA.dt, CB.dt) pair_change
  let patch dx x = match dx with
  | Pair_fst da -> (CA.patch da (fst x), snd x)
  | Pair_snd db -> (fst x, CB.patch db (snd x))
  | Pair_both (da, db) -> (CA.patch da (fst x), CB.patch db (snd x))
  let vc c x = match c with
  | Pair_fst da -> CA.vc da (fst x)
  | Pair_snd db -> CB.vc db (snd x)
  | Pair_both (da, db) -> CA.vc da (fst x) && CB.vc db (snd x)
  let v_to_string x = 
    let (x, y) = x in 
    "(" ^ CA.v_to_string x ^ ", " ^  CB.v_to_string y ^ ")"
  let dv_to_string = function    
  | Pair_fst da -> "Pair_fst (" ^ CA.dv_to_string da ^ ")"
  | Pair_snd db -> "Pair_snd (" ^ CB.dv_to_string db ^ ")"
  | Pair_both (da, db) -> 
    "Pair_both (" ^ CA.dv_to_string da ^ ", " ^ CB.dv_to_string db ^ ")"
end