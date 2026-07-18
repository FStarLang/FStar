module HideRevealUnif
open FStar.Ghost

assume
val t (x:int) : Type0
assume
val f (#x:erased int) (y:t (reveal x)) : unit
let test1 (y:t 17) : unit = f y //F* can now infer the implicit arg here, as below
let test1' (y:t 17) : unit = f #(hide 17) y


assume
val s (x:erased int) : Type0
assume
val g (#x:int) (y: t (hide x)) : unit
let test2 (i:erased int) (y:t i) : unit = g y //F* can now infer the implicit arg here, as below
let test2' (i:erased int) (y:t i) : unit = g #(reveal i) y

(* Testing that the unifier can solve
  hide (reveal x) == x
and
  reveal (hide x) == x *)

#push-options "--no_smt"

let c1 (tt : erased int -> Type) (z : erased int)
       (x : tt (hide (reveal z)))
       : tt z
       = x

let c2 (tt : erased int -> Type) (z : erased int)
       (x : tt z)
       : tt (hide (reveal z))
       = x

let c3 (tt : int -> Type) (z : int)
       (x : tt (reveal (hide z)))
       : tt z
       = x

let c4 (tt : erased int -> Type) (z : erased int)
       (x : tt z)
       : tt (reveal (hide z))
       = x

#pop-options
