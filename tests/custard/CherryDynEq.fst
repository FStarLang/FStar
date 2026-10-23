module CherryDynEq
module U32 = FStar.UInt32
open FStar.All
open FStar.Dyn

(* Issue 4715.  [dyn] is not an eqtype, so only an assumed [hasEq] (or --lax)
   lets a program compare one -- and Cherry has no comparison for it.  The
   test at [cell] has to name the field that leads to the [dyn]. *)
assume val dyn_has_eq : squash (hasEq dyn)

type cell = { d: dyn; n: int }
type wrap = | W : k:int -> c:cell -> wrap | V

let hide (#a: Type) (x: a) : ML a = x

let main () : ML U32.t =
  let d1 = mkdyn (hide 42) in
  let d2 = mkdyn (hide "boxed") in
  let w1 = W 0 { d = d1; n = 1 } in
  let w2 = W 0 { d = d2; n = 1 } in
  if w1 = w2 then 1ul else 0ul
