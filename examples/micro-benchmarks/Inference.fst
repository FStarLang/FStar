module Inference

open FStar.HyperStack
open FStar.HyperStack.ST
module MDM = FStar.Monotonic.DependentMap

(*
 * AR: 02/06: we removed some arguably unnecessary code in the typechecker that
 *            annotated names with the expected types (rather than the types at their
 *              binding sites)
 *            the following testcase fails, since now F* infers a:Type0 rather than
 *              a:eqtype
 *            this is purely coincidental though, nothing fundamentally related to the change
 *            in general, given that eqtype is a refinement of Type, F* may not always
 *              succeed in inferring eqtype, so always better to annotate explicitly
 *)

%Fail
let alloc_fails #a #b #inv (r: erid):
  ST (MDM.t r a b inv)
    (requires (fun h ->
      inv (MDM.empty_partial_dependent_map #a #b) /\
      witnessed (region_contains_pred r) ))
    (ensures (fun h0 x h1 ->
      inv (MDM.empty_partial_dependent_map #a #b) /\
      ralloc_post r (MDM.empty #a #b) h0 x h1))
  = MDM.alloc #a #b #inv #r ()

let alloc (#a:eqtype) #b #inv (r: erid):
  ST (MDM.t r a b inv)
    (requires (fun h ->
      inv (MDM.empty_partial_dependent_map #a #b) /\
      witnessed (region_contains_pred r) ))
    (ensures (fun h0 x h1 ->
      inv (MDM.empty_partial_dependent_map #a #b) /\
      ralloc_post r (MDM.empty #a #b) h0 x h1))
  = MDM.alloc #a #b #inv #r ()


(*
 * The testcase that lead us to remove the typechecker code in question
 *)

assume val merkle_addr:eqtype
assume val is_proper_desc (d a: merkle_addr) : Type0
assume val is_desc_empty (d:merkle_addr) (a:merkle_addr{is_proper_desc d a}) : Type0

//silence the definition not recursive warning
#set-options "--admit_smt_queries true --warn_error -328"
let rec lemma_desc_hash_empty_implies_no_desc 
  (a:merkle_addr)
  (d:merkle_addr{is_desc_empty d a})
: bool
= admit ()
