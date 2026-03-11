open Autoinc.Opbase
open Autoinc.Pprinter

module type Config = sig
  module D : DiffOp
  module In : PPrinter with type t = D.a
  module Out : PPrinter with type t = D.b
  module DIn : PPrinter with type t = D.da
  module DOut : PPrinter with type t = D.db
  val prog : string
end

module Make(C : Config) = struct
  open C
  let init x = 
    let y = D.op x in
    print_endline ("Program: " ^ C.prog);
    Printf.printf "[RC] in = %s; out = %s\n" (In.to_string x) (Out.to_string y)

  let run dx =
    let dy = D.dop dx in
    Printf.printf "[IC] din = %s; dout = %s\n" (DIn.to_string dx) (DOut.to_string dy)

  let rec run_iter = function
  | [] -> ()
  | dx :: dxs -> run dx; run_iter dxs

end

module Example1 = struct
  module N = Autoinc.Nat_change
  module P = Autoinc.Pair_change
  module S = Autoinc.Seq_change
  module Config1 = struct
    module D = StatefulFunctor(N.DiffTimes)
    module In = PairPrinter(N.PPrinter)(N.PPrinter)
    module Out = N.PPrinter
    module DIn = P.ChangePPrintter(N.ChangePPrintter)(N.ChangePPrintter)
    module DOut = SeqPrinter(N.ChangePPrintter)
    let prog = "?x.?y. x * y"
  end
  module M = Make(Config1)
  let () = M.init (N.int_of_nat 3, N.int_of_nat 4)
  let () = M.run (Pair_fst (Add (N.int_of_nat 3)))
  let () = M.run (Pair_snd (Sub (N.int_of_nat 2)))
  let () = M.init (N.int_of_nat 3, N.int_of_nat 6)
  let () = M.run_iter [Pair_fst (Add (N.int_of_nat 3)); Pair_snd (Sub (N.int_of_nat 2))]
end

