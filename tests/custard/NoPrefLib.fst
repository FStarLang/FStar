module NoPrefLib
module U32 = FStar.UInt32

(* Section 115.  A unit built with [--custard_c_no_prefix] publishes its
   names unprefixed, and its header declares them that way.  A consumer
   recomputed the C spelling of an imported name from its own settings, which
   do not mention somebody else's module, and emitted a call to a symbol the
   header it includes does not declare.  The producer's setting travels in
   the `.cui` now. *)
let add1 (x:U32.t) : U32.t = U32.add_mod x 1ul
