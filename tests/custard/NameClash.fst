module NameClash
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* C has no ['], so [step_] and [step'] are both spelled [NameClash_step_].
   Both have internal linkage, so the second is renamed rather than rejected,
   and the fresh name skips [NameClash_step__1], which [step__1] already
   spells.  Each returns a different value, so a call that reached the wrong
   definition makes [main] fail. *)

let step_ (x:U32.t) : U32.t = U32.add_mod x 1ul

let step' (x:U32.t) : U32.t = U32.add_mod x 2ul

let step__1 (x:U32.t) : U32.t = U32.add_mod x 3ul

let main () : ML I32.t =
  if U32.eq (step_ 10ul) 11ul && U32.eq (step' 10ul) 12ul && U32.eq (step__1 10ul) 13ul
  then 0l else 1l
