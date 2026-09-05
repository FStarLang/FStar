module SepLibC
(* Section 42: the upstream unit of the C separate-compilation test.  Nothing
   here refers to SepAppC; the point is that it is compiled once, on its own,
   and SepAppC reuses the result rather than compiling any of it again.

   Four things have to cross the boundary, and each is here for a reason:

   - [point], a struct, because a type defined in two headers that meet in one
     translation unit is an error in C and in C++ alike (section 42.2);
   - [scale], a root, because that is what a C unit's interface offers;
   - [double_it], not a root, because a [static] definition must *not* be
     offered -- the downstream unit compiles its own copy (section 42.1);
   - [origin], a global, because a global is what makes a unit have an
     initializer at all, and the initializer is what has to be namespaced
     (section 42.3). *)

module U32 = FStar.UInt32

type point = { px : U32.t; py : U32.t }

(* Not a [--custard_entry], so [static], so absent from the `.cui`. *)
let double_it (v:U32.t) : U32.t = U32.add_mod v v

let scale (p:point) : point =
  { px = double_it p.px; py = double_it p.py }

let manhattan (p:point) : U32.t = U32.add_mod p.px p.py

(* A struct-valued global.  The compound literal Custard emits for one is not
   a constant expression at file scope, so this is initialized at startup
   rather than statically -- which is exactly the case section 42.3 is about. *)
let origin : point = { px = 3ul; py = 4ul }
