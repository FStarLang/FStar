module KindAbbrev

(* Section 60.3.  The probe for section 57.2, contributed by a reviewer.

   57.2 replaced full normalization with [Weak; HNF] in [Mono.is_arity_aux],
   on the argument that an arity is a [Tm_type] or a [Tm_arrow] --- both head
   shapes --- and that neither is discovered by reducing under a head one
   already has.  The argument is sound but it was only an argument, and the
   cost of it being wrong is the bad kind: [is_arity] returning false for a
   real arity does not reject, it keeps a type binder as a runtime parameter
   and miscompiles.

   What makes it worth a test is that [is_arity_aux] normalizes *exactly
   once* ([not normed && is_arity_aux true env (norm ...)]).  Under full
   normalization one pass reaching a [Tm_type] was guaranteed if one was
   there at all; under [Weak; HNF] it is guaranteed only if head reduction
   alone exposes it.  So the shapes that matter are the ones where the head
   is not immediately present, and all three below are erased correctly.

   [kf 0] is the sharp one: it is section 56's shape one level up, a
   type-level function whose result is a *kind*, so the head appears only by
   reducing an application --- and that has to happen inside the single
   permitted pass.  [eqtype] is a refinement, so it also runs [strip].

   The functions are recursive on purpose.  A first version used plain
   identity functions and Custard constant-folded all three calls away,
   leaving a [main] that compared literals and asserted nothing about the
   binders. *)

module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

let k1 : Type u#1 = Type0
let k2 : Type u#1 = k1
let k3 : Type u#1 = k2
let kf (n : nat) : Type u#1 = Type0

let rec hold_k (a : k3) (x : a) (n : U32.t) : Tot a (decreases (U32.v n)) =
  if U32.eq n 0ul then x else hold_k a x (U32.sub n 1ul)

let rec hold_e (a : eqtype) (x : a) (n : U32.t) : Tot a (decreases (U32.v n)) =
  if U32.eq n 0ul then x else hold_e a x (U32.sub n 1ul)

let rec hold_f (a : kf 0) (x : a) (n : U32.t) : Tot a (decreases (U32.v n)) =
  if U32.eq n 0ul then x else hold_f a x (U32.sub n 1ul)

let main () : ML I32.t =
  let a = hold_k U32.t 7ul 3ul in
  let b = hold_e U32.t 8ul 3ul in
  let c = hold_f U32.t 9ul 3ul in
  if U32.eq a 7ul && U32.eq b 8ul && U32.eq c 9ul then 0l else 1l
