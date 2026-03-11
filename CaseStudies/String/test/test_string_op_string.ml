open Autoinc.String_op

module TestLastIndexOf = struct
  module C = struct let c = 'c' end
  module D = StringLastIndexOf(C)
  open D 

  let test_cases = List.map (fun (a, b) -> (string_to_list a, b))
    [ ("abashfahbcb", DString.Noc)
    ; ("abashfahbcb", ins 1 "kkkk")
    ; ("abashfahbcb", del 2 3)
    ; ("abashfahbcb", del 9 1)
    ]

end

module TestLastIndexOfHttps = struct
  module C = struct let c = '=' end
  module D = StringLastIndexOf(C)
  open D 
  let url = "   https://www.google.com/search?q=url&oq=url&gs_lcrp=EgZjaHJvbWUyBggAEEUYOTIGCAEQRRg8MgYIAhBFGD0yBggDEEUYPNIBCDEwOTBqMGo3qAIAsAIA&sourceid=chrome&ie=UTF-8"
  let test_cases = List.map (fun (a, b) -> (string_to_list a, b))
    [ (url, ins 1 "  ")
    ; (url, del 10 20)
    ; (url, ins 30 "mainz")
    ; (url, del 149 1)
    ]

end

