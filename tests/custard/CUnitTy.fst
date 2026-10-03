module CUnitTy
open FStar.All

(* Section 123.  A [ref unit] is a [custard_unit *], and a type reaches the
   header whether or not any signature is public, so this is the case where
   the typedef has to be in the header. *)
noeq type box = { cell : ref unit; tag : UInt32.t }

let mk () : ML box = { cell = alloc (); tag = 0ul }

let main () : ML UInt32.t =
  let b = mk () in
  b.cell := ();
  b.tag
