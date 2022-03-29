module Part1.Poly

let id (a:Type) (x:a) : a = x


let _ : bool = id bool true
let _ : bool = id bool false
let _ : int = id int (-1)
let _ : nat = id nat 17
let _ : string = id string "hello"
let _ : int -> int = id (int -> int) (id int)

val apply (a b:Type) (f:a -> b) : a -> b
val compose (a b c:Type) (f: b -> c) (g : a -> b) : a -> c

let apply = admit()
let compose = admit()

val twice (a:Type) (f: a -> a) (x:a) : a
let twice = admit()
