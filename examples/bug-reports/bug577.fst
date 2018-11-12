module Bug577

type step : int -> Type =

noeq type multi (r:int -> Type) : int -> Type =
| Multi_step : x:int -> r x -> multi r x

val aux : e:int -> step e -> Tot bool
let aux e h = magic()

val steps_preserves_red : e:int -> b:multi step e -> Tot bool
let steps_preserves_red e h =
  match h with
  | Multi_step _ xx -> aux e xx
