open Change

module TripleChange(CA: Change)(CB: Change)(CC: Change) = struct
  type t = CA.t * CB.t * CC.t
  type dt = CA.dt * CB.dt * CC.dt
  let vc (dt_a, dt_b, dt_c) (t_a, t_b, t_c) = 
    CA.vc dt_a t_a && CB.vc dt_b t_b && CC.vc dt_c t_c
  let patch (dt_a, dt_b, dt_c) (t_a, t_b, t_c) = 
    let t_a' = CA.patch dt_a t_a in
    let t_b' = CB.patch dt_b t_b in
    let t_c' = CC.patch dt_c t_c in
    (t_a', t_b', t_c')

  let v_to_string (t_a, t_b, t_c) = 
    "(" ^ CA.v_to_string t_a ^ ", " ^ CB.v_to_string t_b ^ ", " ^
    CC.v_to_string t_c ^ ")"
  let dv_to_string (t_a, t_b, t_c) = 
    "(" ^ CA.dv_to_string t_a ^ ", " ^ CB.dv_to_string t_b ^ ", " ^
    CC.dv_to_string t_c ^ ")"    

end