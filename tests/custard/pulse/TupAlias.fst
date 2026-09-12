(* Section 109.  Section 106 compared the built-in representation rules named
   before a reduction with those named after it, which finds a rule the
   reduction destroyed -- so long as the written form names it.  A type
   abbreviation is exactly what makes it absent: [type pack a = option (array
   a)] names no rule at either endpoint, the rule being introduced by
   unfolding [pack] and erased by unfolding [array] inside the one
   normalization.  Both keys came out [option array'], and [fst] got one
   specialization for two incompatible tuple types again.

   [explicit_control] is the same type with [pack] spelled out, which is why
   it worked: there the rule is visible at the first endpoint.  The walk now
   unfolds as it goes and stops where a rule is, so it reaches the same place
   from the abbreviation. *)
module TupAlias

module U = FStar.UInt32
module A = Pulse.Lib.Array

type element =
  | First
  | Second

type pack (a:Type0) = option (A.array a)

let fst_both (x : U.t & pack element) (y : U.t & pack bool) : U.t =
  U.add_mod (fst x) (fst y)

let snd_both (x : pack element & U.t) (y : pack bool & U.t) : U.t =
  U.add_mod (snd x) (snd y)

(* The same types with the abbreviation spelled out: the control that worked
   throughout, and still must. *)
let explicit_control (x : U.t & option (A.array element))
                     (y : U.t & option (A.array bool)) : U.t =
  U.add_mod (fst x) (fst y)

(* A chain of two abbreviations, which is what the fuel is for. *)
type packed (a:Type0) = pack a

let chain_both (x : U.t & packed element) (y : U.t & packed bool) : U.t =
  U.add_mod (fst x) (fst y)

let main () : FStar.All.ML FStar.Int32.t =
  let e : pack element = None in
  let b : pack bool = None in
  let n = fst_both (1ul, e) (2ul, b) in
  let m = snd_both (e, 3ul) (b, 4ul) in
  let p = explicit_control (1ul, e) (2ul, b) in
  let q = chain_both (1ul, e) (2ul, b) in
  if U.eq n 3ul && U.eq m 7ul && U.eq p 3ul && U.eq q 3ul then 0l else 1l
