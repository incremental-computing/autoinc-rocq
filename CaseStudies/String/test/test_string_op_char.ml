open Autoinc.String_change
open Autoinc.Op
open Autoinc.Seq_change
open Base

module TestTrimLeft = struct
  module D = DiffTrimLeft
  open StringChange_1
  let test_cases = [
    ("abc", Ins(0, ' '));
    ("abc", Ins(0, '0'));
    ("abc", Ins(1, ' '));
    (" abc", Ins(0, ' '));
    (" a bc", Del 1);
  ]
end

module TestIndexOf = struct
  module P = struct let pat = "ab" end
  module D = DiffIndexOf(P)
  open StringChange_1
  let test_cases = [
    ("abc", Ins(0, ' '));
    ("abc", Ins(0, '0'));
    ("abc", Ins(1, ' '));
    (" abc", Ins(0, ' '));
    (" a bc", Del 1);
    (" abc", Ins(3, 'x'))
  ]
end

module TestSubstring = struct
  open StringChange_1
  module D = DiffSubString
  let test_cases = [
    (("abcd", 1, 2), (Noc, 0, 1));
    (("abcd", 1, 2), (Noc, 1, 0));
    (("abcd", 1, 2), (Noc, 1, 1));
    (("abcd", 1, 2), (Ins(0, 'x'), 0, 0));
    (("abcd", 1, 2), (Ins(3, 'x'), 0, 0));
    (("abcd", 1, 2), (Ins(2, 'x'), 0, 0));
    (("abcd", 1, 3), (Ins(1, 'x'), 0, 0));
    (("abcd", 1, 2), (Del 0, 0, 0));
    (("abcd", 1, 2), (Del 3, 0, 0));
    (("abcd", 1, 2), (Del 2, 0, 0));
    (("abcde", 1, 3), (Del 1, 0, 0));
    (("abcde", 1, 4), (Del 2, 0, 0));
    (("abcde", 0, 3), (Del 1, 0, 0));

  ]
end




module SecureUrl = struct
  (*
  def isSecured(url: String) =
    val trimmed    = trimLeft(url)
    val protocolIx = indexOf(trimmed, ':')
    val protocol   = substring(trimmed, 0, protocolIx)
    startsWith(protocol, "https")
  *)
  let url = "   https://www.google.com/search?q=url&oq=url&gs_lcrp=EgZjaHJvbWUyBggAEEUYOTIGCAEQRRg8MgYIAhBFGD0yBggDEEUYPNIBCDEwOTBqMGo3qAIAsAIA&sourceid=chrome&ie=UTF-8"

  open Autoinc.Opbase
  open Autoinc.Compress
  open Autoinc.Seq_change
  open Autoinc.Triple_change
  module INT = Autoinc.Int_change
  module S = struct let pat = ":" end
  module Trimmed = StatefulFunctor(DiffTrimLeft)
  module ProtocolIx_ = Lift(StatefulFunctor(DiffIndexOf(S)))
  module Substring = StatefulFunctor(DiffSubString) (* f : string * int * int -> string *)
  module ProtocolIxList = Seq(ProtocolIx_)(Trimmed)
  module CompressInt = StatelessFunctor(StatelessCompress(INT.IntChange)(INT.M))
  module ProtocolIx = Seq(CompressInt)(ProtocolIxList)
  module H = ID(INT.IntChange)
  module DString = struct type ty = string ;; type dty = StringChange_1.dt ;; let noc = StringChange_1.Noc end
  module DInt = struct type ty = int ;; type dty = int ;; let noc = 0 end

  module SubstringOp = Lift_3_1(DString)(DInt)(DInt)(Substring)
  module Protocol = Triple(Trimmed)(ID(INT.IntChange))(ProtocolIx)(SubstringOp)
  module ProtocolAPI = struct 
    type a = string
    type b = string
    type da = StringChange_1.dt
    type db = SubstringOp.db
    let op str = Protocol.op (str, 0, str)
    let dop dstr = Protocol.dop (dstr, 0, StringChange_1.Noc)
  end
  module P = struct type t = StringChange_1.dt ;; let to_string = StringChange_1.dv_to_string end
  module Printer = Autoinc.Pprinter.SeqPrinter(P)

end

module RunSecureUrl = struct
  module K = SeqChange(StringChange_1)

  let run () = 
    let s = SecureUrl.ProtocolAPI.op SecureUrl.url in
    let dout1 = SecureUrl.ProtocolAPI.dop StringChange_1.Noc in
    let in1 = StringChange_1.patch (StringChange_1.Noc) SecureUrl.url in
    let s1 = K.patch (List.concat dout1) s in
    let dout2 = SecureUrl.ProtocolAPI.dop (StringChange_1.Ins(0, ' ')) in
    let in2 = StringChange_1.patch (StringChange_1.Ins(0, ' ')) in1 in
    let s2 = K.patch (List.concat dout2) s1 in
    let dout3 = SecureUrl.ProtocolAPI.dop (StringChange_1.Del(6)) in
    let in3 = StringChange_1.patch (StringChange_1.Del(6)) in2 in
    let s3 = K.patch (List.concat dout3) s2 in
    let dout4 = SecureUrl.ProtocolAPI.dop (StringChange_1.Ins(20, 'a')) in
    let in4 = StringChange_1.patch (StringChange_1.Ins(20, 'a')) in3 in
    let s4 = K.patch (List.concat dout4) s3 in
    print_endline s;
    print_endline (SecureUrl.Printer.to_string (List.concat dout1));
    print_endline (in1 ^ " -> " ^ s1);
    print_endline (SecureUrl.Printer.to_string (List.concat dout2));
    print_endline (in2 ^ " -> " ^ s2);
    print_endline (SecureUrl.Printer.to_string (List.concat dout3));
    print_endline (in3 ^ " -> " ^ s3);
    print_endline (SecureUrl.Printer.to_string (List.concat dout4));
    print_endline (in4 ^ " -> " ^ s4);
end


  



