
module BoolChange = struct
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