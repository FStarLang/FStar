module CNoClosure

module U32 = FStar.UInt32

(* [twice] is passed a function it did not know at extraction time, and the
   argument is not marked [@@@monomorphize], so it survives as a first-class
   value.  C has no closures: the backend must reject this (error 368) rather
   than emit something that cannot represent the captured [n]. *)

let twice (f: U32.t -> U32.t) (x: U32.t) : U32.t = f (f x)

let main () : U32.t =
  let n = 3ul in
  twice (fun x -> U32.add_mod x n) 1ul
