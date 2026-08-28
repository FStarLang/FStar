module KrmlPrivateTest

open FStar.UInt32

(* [hidden] is not declared in the interface, so by default it is tagged
   with the internal KrmlPrivate attribute and Karamel emits it as a
   [static] C function. With --ext no_krml_private the tag is not added
   and the function is externally visible. *)
let hidden (x:UInt32.t) : UInt32.t = x `add_mod` 1ul

let exposed x = hidden x
