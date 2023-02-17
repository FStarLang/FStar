module Steel.ST.C.Model.Ref

// FIXME: in fact, to avoid those explicit coercions below, we should
// swap Steel.ST.C.Model.Ref.fst and Steel.C.Model.Ref.fst for the
// non-view operations, thus benefitting from the automatic effect
// liftings

module STC = Steel.ST.Coercions
module SR = Steel.C.Model.Ref

let ref_alloc
  p x
= STC.coerce_steel (fun _ -> SR.ref_alloc p x)

let ref_free
  r
= STC.coerce_steel (fun _ -> SR.ref_free r)

let gfocus
  r l s x
= STC.coerce_ghost (fun _ -> SR.gfocus r l s x)

let focus
  r l s x
= STC.coerce_atomic (fun _ -> SR.focus r l s x)

let unfocus
  r r' l x
= STC.coerce_ghost (fun _ -> SR.unfocus r r' l x)

let split r xy x y
= STC.coerce_ghost (fun _ -> SR.split r xy x y)

let gather r x y
= STC.coerce_ghost (fun _ -> SR.gather r x y)

let ref_read r
= STC.coerce_steel (fun _ -> SR.ref_read r)

let ref_upd
  r x y f
= STC.coerce_steel (fun _ -> SR.ref_upd r x y f)
