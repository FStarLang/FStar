module PolyExtern

open FStar.All
module U32 = FStar.UInt32

(* Section 63.3.  A polymorphic [assume val]: the symbol is realized in C, and
   the type it is realized at comes from the call site.

   Before the fix this was error 368 -- the declaration path read its own type
   raw, so the type variable reached the backend still a variable -- and the
   message blamed a monomorphization bug, which was doubly wrong: nothing was
   broken, and monomorphization had never been asked to do anything.

   The property that matters is that two instantiations are two symbols.  One
   [extern] shared by [box_u32] and [box_pair] would be a single C function
   receiving two different types, which is the miscompilation, not the fix. *)

type pair = { fst: U32.t; snd: U32.t }

assume val identity (#a:Type0) (x:a) : a

let main () : ML U32.t =
  let x = identity 7ul in
  let p = identity ({ fst = 3ul; snd = 4ul }) in
  if U32.eq x 7ul && U32.eq p.fst 3ul && U32.eq p.snd 4ul then 0ul else 1ul
