module Test

module DM = FStar.DependentMap
module S  = FStar.Struct
module HST = FStar.HyperStack.ST

type point_fd =
| X
| Y

let point_struct = DM.t point_fd (function
| X -> int
| Y -> int
)

let point = S.struct_ptr point_struct

type colored_object_fd =
| Carrier
| Color

let colored_object_struct (t: Type) = DM.t colored_object_fd (function
| Carrier -> t
| Color -> bool
)

let colored_object (t: Type) = S.struct_ptr (colored_object_struct t)

let colored_point = colored_object point_struct

let flip
  (p: colored_point)
: HST.Stack unit
  (requires (fun h -> S.live h p))
  (ensures (fun h0 _ h1 -> 
      S.live h0 p
    /\ S.live h1 p
    /\ S.modifies_1 p h0 h1
    /\ S.as_value h1 (S.gfield (S.gfield p Carrier) X) == S.as_value h0 (S.gfield (S.gfield p Carrier) Y)
    /\ S.as_value h1 (S.gfield (S.gfield p Carrier) Y) == S.as_value h0 (S.gfield (S.gfield p Carrier) X)
    /\ S.as_value h1 (S.gfield p Color) == not (S.as_value h0 (S.gfield p Color))
    ))
= let pt = S.field p Carrier in
  let x = S.read (S.field pt X) in
  let y = S.read (S.field pt Y) in
  let color = S.read (S.field p Color) in
  S.write (S.field pt X) y;
  S.write (S.field pt Y) x;
  S.write (S.field p Color) (not color)

let flip'
  (p: colored_point)
: HST.Stack unit
  (requires (fun h -> S.live h p))
  (ensures (fun h0 _ h1 -> 
      S.live h0 p
    /\ S.live h1 p
    /\ S.modifies_1 p h0 h1
    /\ S.as_value h1 (S.gfield (S.gfield p Carrier) X) == S.as_value h0 (S.gfield (S.gfield p Carrier) Y)
    /\ S.as_value h1 (S.gfield (S.gfield p Carrier) Y) == S.as_value h0 (S.gfield (S.gfield p Carrier) X)
    /\ S.as_value h1 (S.gfield p Color) == not (S.as_value h0 (S.gfield p Color))
    ))
= let pt = S.field p Carrier in
  let x = S.read (S.field pt X) in
  let y = S.read (S.field pt Y) in
  S.write (S.field pt X) y;
  S.write (S.field pt Y) x;
  let color = S.read (S.field p Color) in
  S.write (S.field p Color) (not color)
