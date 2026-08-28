module CTypeField

(* Section 30.5.  A [Type0] *field* of a record, projected in a type position
   inside a function that is specialized on the record.

   [s.t] is stuck: a projector is not a type constructor, so [ty_of_typ] used
   to hand it to [ty_of_fv] and get [any] back, and [pick] came out over
   [any] with a reinterpretation at each end.  [specialize] has already
   substituted the concrete record for [s], so unfolding the projector and
   letting iota meet the constructor gives the ground type -- and the
   scrutinee has to unfold by delta too, since [s0] is a top-level name and
   iota cannot see through one.

   [t] is erased, so [spec] keeps only [sz] and collapses to it (section 5.2);
   that is deliberate, and it is what keeps the record's *own* declaration out
   of the picture.  A record whose surviving fields still mention the type
   field is the case section 30.3 records as unsupported, and this is not it.

   [main] checks its own answer, so a wrong reinterpretation is a nonzero exit
   rather than something to read out of the generated C. *)

module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32

noeq type spec = { t: Type0; sz: SZ.t }

let s0 : spec = { t = U8.t;  sz = 3sz }
let s1 : spec = { t = U32.t; sz = 7sz }

(* Not the identity, and not a forwarder either (section 27), so it survives
   as a real function whose signature is the thing under test. *)
let pick ([@@@monomorphize] s: spec) (c: bool) (x: s.t) (y: s.t) : s.t =
  if c then x else y
let size ([@@@monomorphize] s: spec) : SZ.t = s.sz

let main () : U32.t =
  let a = pick s0 true 200uy 0uy in
  let b = pick s1 false 0ul 70000ul in
  if U8.(a =^ 200uy) && U32.(b =^ 70000ul)
     && SZ.(size s0 =^ 3sz) && SZ.(size s1 =^ 7sz)
  then 0ul else 1ul
