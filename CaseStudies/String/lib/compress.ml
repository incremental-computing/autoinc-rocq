open Op
open Change
open Monoid
open Seq_change


module StatelessCompress(C : Change)(M : Monoid with type t = C.dt) = struct
  module CA = SeqChange(C)
  module CB = C
  let f = fun x -> x
  let df = List.fold_left M.mappend M.mempty
end