module DropRun
module U32 = FStar.UInt32
module G = FStar.Ghost

(* Section 81.  [#p] is unit-shaped and [#f] is erased, and neither is last.
   [g] is a top-level partial application, so section 25.3 declines to
   eta-expand it and its binders are filtered against the classification
   rather than against [polycs] -- which is where the definition and its call
   sites used to disagree about the unit one. *)
inline_for_extraction
let gen (et: Type0) (bm: U32.t) (b: U32.t)
        (#p: squash (b == b)) (#f: G.erased nat) (c: U32.t) : U32.t =
  U32.logxor b c

let g = gen U32.t 32ul

let dispatch (b: U32.t) (#p: squash (b == b)) (#f: G.erased nat) (c: U32.t) : U32.t =
  g b #p #f c

let main () : FStar.All.ML FStar.Int32.t =
  let r = dispatch 6ul #() #(G.hide 0) 3ul in
  if r = 5ul then 0l else 1l
