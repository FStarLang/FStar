module NameWidth

(* Section 30.15.  An instantiation name is built from its arguments, and an
   argument that is itself an instantiation contributes the name it was given
   -- so a type that accumulates doubles the name at every level.  Unbounded,
   this file at depth 12 emitted a C identifier of 57,361 characters, and C99
   promises to distinguish only the first 63 of an internal one.

   The NOGREP is nine nested [tuple2]s spelled out in a single name, which is
   what the depth below would produce with no width bound. *)

module U32 = FStar.UInt32

noeq type env (t:Type0) = { v: t; g: t -> U32.t }

let extend (#t:Type0) ([@@@FStar.Attributes.monomorphize] e: env t) : env (t & t) =
  { v = (e.v, e.v);
    g = (fun (p: t & t) -> U32.add_mod (e.g (fst p)) (e.g (snd p))) }

let e0 : env U32.t = { v = 1ul; g = (fun x -> x) }
let e1 = extend e0
let e2 = extend e1
let e3 = extend e2
let e4 = extend e3
let e5 = extend e4
let e6 = extend e5
let e7 = extend e6
let e8 = extend e7

let go (u:U32.t) : U32.t = U32.add_mod u (e8.g e8.v)

let main () : U32.t = if U32.(go 0ul =^ go 0ul) then 0ul else 1ul
