module TailLinkLib
(* The upstream unit of #4771.  Two functions of more than one argument, so
   that a downstream wrapper forwarding its own parameters to them is
   eta-reduced to a partial application. *)
module U32 = FStar.UInt32

let add (a b: U32.t) : U32.t = U32.add_mod a b

let between (lo x hi: U32.t) : bool = U32.lte lo x && U32.lte x hi
