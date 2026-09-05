module KindStar

(* Section 60.4.  The probe for the *other* half of section 57.2.

   57.2 changed two step lists, [Mono.is_arity_aux] and [Mono.is_star_aux].
   A reviewer verified the first thoroughly and reported, honestly, that they
   could not reach the second: their attempt used a binder of an abbreviated
   higher kind, which F* rejects outright.  Measuring it settled the
   question --- with [UnfoldUntil delta_constant] deleted from [is_star_aux]
   alone, the whole of tests/custard still passed.  Nothing exercised it.

   The difference between the two predicates is what the answer is used for.
   [is_arity] asks whether a binder is erased; [is_star_aux] asks whether an
   erased binder can become a *parameter of a target type*, which only a
   binder of kind [Type] can be (section 5.0).  So reaching it needs a
   **type** parameterized by a name that unfolds to [Type], not a function:
   [KindAbbrev]'s binders are all consulted through [is_arity] and are
   decided before [is_star_aux]'s normalization is needed.

   With that step removed, [k2] does not unfold, [box]'s parameter is not a
   type parameter, and [v]'s representation is lost -- the extraction fails
   rather than miscompiling, because [--custard_warn_any] is on.  With it
   present, [box] is a one-field record and collapses to its field
   (section 8), so the assertion below is on the monomorphized [get]. *)

module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

let k1 : Type u#1 = Type0
let k2 : Type u#1 = k1

noeq type box (a : k2) = { v : a }

let mk (a : k2) (x : a) : box a = { v = x }
let get (a : k2) (b : box a) : a = b.v

let main () : ML I32.t =
  let b = mk U32.t 7ul in
  if U32.eq (get U32.t b) 7ul then 0l else 1l
