module Library
module U32 = FStar.UInt32

(* Extracted with --custard_entry and no --custard_main: the generated code is
   meant to be called from a hand-written wrapper, so nothing runs on startup.
   [double] is reachable only from [scale], which is reachable only because it
   is a root. *)

let double (x:U32.t) : U32.t = U32.add_mod x x

let scale (x:U32.t) (n:U32.t) : U32.t =
  if U32.eq n 0ul then x else double x

(* Not a root and not reachable from one: it must not be extracted. *)
let unused (x:U32.t) : U32.t = U32.sub_mod x 1ul
