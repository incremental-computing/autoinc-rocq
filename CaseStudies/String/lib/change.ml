module type Change = sig
  type t
  type dt
  val vc : dt -> t -> bool  
  val patch : dt -> t -> t

  val v_to_string : t -> string
  val dv_to_string : dt -> string 
end