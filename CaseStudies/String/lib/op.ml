open Change

module type StatelessDiffOp = sig
  module CA : Change
  module CB : Change
  val f : CA.t -> CB.t
  val df : CA.dt -> CB.dt
end

module type StatefulDiffOp = sig
  module CA : Change
  module CB : Change
  module CS : Change with type dt = CA.dt
  val f : CA.t -> CB.t
  val df : CA.dt -> CS.t -> CB.dt
  val init : CA.t -> CS.t
end

module type StatefulDiffOpSingleFun = sig
  module CA : Change
  module CB : Change
  type s
  val f : CA.t -> CB.t
  val df : CA.dt -> s -> CB.dt * s
  val init : CA.t -> s
end