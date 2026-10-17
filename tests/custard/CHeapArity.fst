module CHeapArity
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* Section 135 on the C backend, which keeps dropping erased binders
   everywhere: an arrow behind more than eight abbreviations (FStarLang/FStar#4650)
   is still unfolded to the end, so the definition and its call agree; and a
   record field holding a top-level function keeps the C convention. *)

type t0 = (#p:squash True -> U32.t -> U32.t)
type t1 = unit -> t0
type t2 = unit -> t1
type t3 = unit -> t2
type t4 = unit -> t3
type t5 = unit -> t4
type t6 = unit -> t5
type t7 = unit -> t6
type t8 = unit -> t7
type t9 = unit -> t8
type t10 = unit -> t9
type t11 = unit -> t10

let a (#p:squash True) (x:U32.t) : U32.t = x
let deep : t11 = fun _ _ _ _ _ _ _ _ _ _ _ -> a
let deep8 : t8 = fun _ _ _ _ _ _ _ _ -> a

noeq type ops = { f : x:U32.t -> #p:squash True -> y:U32.t -> U32.t; g : unit -> U32.t }
let add (x:U32.t) (#p:squash True) (y:U32.t) : U32.t = U32.add_mod x y
let seven () : U32.t = 7ul
let r : ops = { f = add; g = seven }

let main () : ML I32.t =
  if U32.eq (deep () () () () () () () () () () () #() 11ul) 11ul &&
     U32.eq (deep8 () () () () () () () () #() 8ul) 8ul &&
     U32.eq (r.f 3ul 4ul) (r.g ())
  then 0l else 1l
