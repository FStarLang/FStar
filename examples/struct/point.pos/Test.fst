module Test

module DM = FStar.DependentMap
module S  = FStar.Pointer
module HST = FStar.ST

type point_fd =
| X
| Y
| Color

let point_struct = DM.t point_fd (function
| X -> int
| Y -> int
| Color -> bool
)

let point = S.pointer point_struct

let flip
  (p: point)
: HST.Stack unit
  (requires (fun h -> S.live h p))
  (ensures (fun h0 _ h1 -> 
      S.live h0 p
    /\ S.live h1 p
    /\ S.modifies_1 p h0 h1
    /\ S.gread h1 (S.gfield p X) == S.gread h0 (S.gfield p Y)
    /\ S.gread h1 (S.gfield p Y) == S.gread h0 (S.gfield p X)
    /\ S.gread h1 (S.gfield p Color) == not (S.gread h0 (S.gfield p Color))
    ))
= let x = S.read (S.field p X) in
  let y = S.read (S.field p Y) in
  let color = S.read (S.field p Color) in
  S.write (S.field p X) y;
  S.write (S.field p Y) x;
  S.write (S.field p Color) (not color)

let flip'
  (p: point)
: HST.Stack unit
  (requires (fun h -> S.live h p))
  (ensures (fun h0 _ h1 -> 
      S.live h0 p
    /\ S.live h1 p
    /\ S.modifies_1 p h0 h1
    /\ S.gread h1 (S.gfield p X) == S.gread h0 (S.gfield p Y)
    /\ S.gread h1 (S.gfield p Y) == S.gread h0 (S.gfield p X)
    /\ S.gread h1 (S.gfield p Color) == not (S.gread h0 (S.gfield p Color))
    ))
= let x = S.read (S.field p X) in
  let y = S.read (S.field p Y) in
  S.write (S.field p X) y;
  S.write (S.field p Y) x;
  let color = S.read (S.field p Color) in
  S.write (S.field p Color) (not color)
