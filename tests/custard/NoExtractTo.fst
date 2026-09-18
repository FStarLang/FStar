(* Section 126.3.  [@@noextract_to] is the backend-specific half of
   [noextract]: the string it carries is a codegen name, and the definition is
   dropped only when that name is the backend in hand.  In the wild it says
   "this one has a hand-written C implementation" -- FStar.UInt128,
   FStar.SizeT and FStar.Endianness all use it that way.

   This module is extracted twice, to OCaml and to C, and each leg checks that
   the *other* leg's definition survived as well as that its own is gone.  An
   attribute that dropped everything would pass a one-sided test.

   Both definitions are dropped as *roots*, not as uses, so [main] calls
   neither; the test returns zero through the exit code rather than printing,
   since direct-to-C has no krmllib and so no [print_string]. *)
module NoExtractTo
open FStar.All

module U32 = FStar.UInt32

[@@noextract_to "krml"]
let only_ocaml (x:U32.t) : U32.t = U32.add_mod x 1ul

[@@noextract_to "OCaml"]
let only_c (x:U32.t) : U32.t = U32.add_mod x 2ul

let kept (x:U32.t) : U32.t = U32.add_mod x 3ul

let main () : ML Int32.t =
  if U32.eq (kept 4ul) 7ul then 0l else 1l
