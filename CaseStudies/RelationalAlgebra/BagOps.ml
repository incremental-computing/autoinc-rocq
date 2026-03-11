open BagOp.Bag
open BagOp.Pair

module Select = BagOp.IncSelect
module Product = BagOp.IncProduct
module UnionAll = BagOp.IncUnionAll
module Join = BagOp.IncJoin
module HashJoin = BagOp.IncHashJoin
module Aggregate = BagOp.IncAggregate
module Project = BagOp.IncProject

module SelectDiffOp = 
  functor (P : Select.SelectParams) -> struct
    open Select.IncSelect(P)
    type  a = P.a bag
    type  b = P.a bag
    let  op = f
    type da = P.a bag_change
    type db = P.a bag_change
    let dop = delta_f
end

module UnionAllDiffOp = 
  functor (P : UnionAll.UnionAllParams) -> struct
    open UnionAll.IncUnionAll(P)
    type  a = P.a bag
    type  b = P.a bag
    let  op = f
    type da = (P.a bag_change, P.a bag_change) pair_change
    type db = P.a bag_change list
    let dop = delta_f
end

module ProjectDiffOp =
  functor (P : Project.ProjectParams) -> struct
    open Project.IncProject(P)
    type a = P.a bag
    type b = P.b bag
    let op = f
    type da = P.a bag_change
    type db = P.b bag_change
    let dop = delta_f
end

module ProductDiffOp = 
  functor (P : Product.ProductParams) -> struct
    open P
    open Product.IncProduct(P)
    type  a = (t1 bag) * (t2 bag)
    type  b = (t1 * t2) bag
    let  op = f
    type da = (t1 bag_change, t2 bag_change) pair_change
    type db = (t1 * t2) bag_change list
    let state = ref (init init_input)
    let dop da = 
      let current = !state in
      state := delta_st da current;
      delta_f da current
end

module JoinDiffOp = 
  functor (P : Join.JoinParams) -> struct
    open P
    open Join.JoinOp(P)
    type a  = l bag * r bag
    type b  = (l * r) bag
    let  op = f
    type da = (l bag_change, r bag_change) pair_change
    type db = (l * r) bag_change list
    let state = ref (init init_input)
    let dop da = 
      let cst = !state in
      state := delta_st da cst;
      delta_f da cst
end

module HashJoinDiffOp = 
  functor (P : HashJoin.JoinParams) -> struct
    open P
    open HashJoin.JoinOp(P)
    type a  = l bag * r bag
    type b  = (l * r) bag
    let  op = f
    type da = (l bag_change, r bag_change) pair_change
    type db = (l * r) bag_change list
    let state = ref (init init_input)
    let dop da = 
      let cst = !state in
      state := delta_st da cst;
      delta_f da cst
end

module AggregateDiffOp = 
  functor (PreOrd : Aggregate.STRICT_PRE_ORDER) -> 
  functor (Join:sig
    val join : PreOrd.coq_E -> PreOrd.coq_E -> PreOrd.coq_E
  end) ->
  functor (Diff:sig
    type delta_E
    val diff : PreOrd.coq_E -> PreOrd.coq_E -> delta_E
  end) ->
    functor (P : sig val init_input : PreOrd.coq_E bag end) ->
  struct
    open Aggregate.DatalogAggregation(PreOrd)(Join)(Diff)
    type a = PreOrd.coq_E bag
    type b = PreOrd.coq_E
    let op = f
    type da = PreOrd.coq_E bag_change
    type db = Diff.delta_E
    let state = ref (init P.init_input)
    let dop da = 
      let cst = !state in
      state := delta_st da cst;
      delta_f da cst
end
