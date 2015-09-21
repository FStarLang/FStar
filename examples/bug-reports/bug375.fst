module Curried

val foo : unit -> unit -> unit
let foo a b = ()

val foo2: unit -> (unit -> unit)
let foo2 a b = ()

type bar = unit -> unit 

val foo3 : unit -> bar
let foo3 a b = ()
