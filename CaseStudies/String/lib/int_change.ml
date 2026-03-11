module IntChange = struct
  type t = int
  type dt = int
  let patch dt t = dt + t
  let vc _ _ = true
  let v_to_string = Int.to_string
  let dv_to_string = Int.to_string

end

module M = struct
  type t = int
  let mappend x y = x + y
  let mempty = 0
end