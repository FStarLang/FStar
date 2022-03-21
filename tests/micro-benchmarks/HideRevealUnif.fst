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
