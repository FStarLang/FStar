module TypeClasses

class foo 'a = { test :'a -> string }

val ee (#a: Type) {| dict: foo a |} : unit
let ee {| dict: foo 'a |} = ()

val ff (#a: Type) {| _: foo a |} : unit
let ff {| _: foo 'a |} = ()

val gg: #a: Type -> {| foo a |} -> unit
let gg {| foo 'a |} = ()

val ee': #a: Type -> _: int -> {| dict: foo a |} -> int -> unit
let ee' x {| dict: foo 'a |} y = ()

val ff' (#a: Type) (_: int) {| _: foo a |} (_: int) : unit
let ff' x {| _: foo 'a |} y = ()

val gg': #a: Type -> int -> {| foo a |} -> int -> unit
let gg' x {| foo 'a |} y = ()
