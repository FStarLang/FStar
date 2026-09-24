module SepLibK
(* Section 42.6: the upstream unit of the karamel separate-compilation test.
   The shape is SepLibC's, deliberately, because the point of the section is
   that a `.cui` written for one backend means the same thing on the other --
   a unit is a unit, and only the printer differs.

   What differs is what crossing the boundary *costs*.  On the C backend an
   imported declaration is an [extern] line Custard writes itself; here it is
   a karamel [DExternal], which is what karamel's own [-library] flag rewrites
   a definition into.  So the four things below are each here to pin one half
   of that rewrite: a struct that karamel must still *declare* downstream
   (karamel keeps [DType] under [-library]), two functions that it must not
   define, and a global that it must neither define nor initialize. *)

module U32 = FStar.UInt32

type point = { px : U32.t; py : U32.t }

let double_it (v:U32.t) : U32.t = U32.add_mod v v

let scale (p:point) : point =
  { px = double_it p.px; py = double_it p.py }

let manhattan (p:point) : U32.t = U32.add_mod p.px p.py

let origin : point = { px = 3ul; py = 4ul }
