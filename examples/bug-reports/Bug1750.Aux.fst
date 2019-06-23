module Bug1750.Aux

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MDM = FStar.Monotonic.DependentMap
module DM = FStar.DependentMap

assume
val pre_dhi :eqtype

//This example tests the need for IsToFun axioms
//for inductive type constructors
//Without those axioms, this example (inspired by mitls-fstar/CommonDH) fails.

noeq
type ilog_entry (i:pre_dhi) =
  | Corrupt

#reset-options "--max_fuel 0 --max_ifuel 0"
let test (log:MDM.map pre_dhi ilog_entry) (k:pre_dhi) (v:ilog_entry k) : Tot unit =
  let log1 = MDM.upd #pre_dhi #ilog_entry log k v in
  assert (Some? (MDM.sel #pre_dhi #ilog_entry log1 k))
