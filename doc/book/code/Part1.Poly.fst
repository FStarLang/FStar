module Part1.Poly

//SNIPPET_START: id
let id (a:Type) (x:a) : a = x
//SNIPPET_END: id

//SNIPPET_START: id applications
let _ : bool = id bool true
let _ : bool = id bool false
let _ : int = id int (-1)
let _ : nat = id nat 17
let _ : string = id string "hello"
let _ : int -> int = id (int -> int) (id int)
//SNIPPET_END: id applications

//SNIPPET_START: sig apply_and_compose
val apply (a b:Type) (f:a -> b) : a -> b
val compose (a b c:Type) (f: b -> c) (g : a -> b) : a -> c
//SNIPPET_END: sig apply_and_compose

//SNIPPET_START: apply_and_compose
let apply a b f = fun x -> f x
let compose a b c f g = fun x -> f (g x)
//SNIPPET_END: apply_and_compose

//SNIPPET_START: sig twice
val twice (a:Type) (f: a -> a) (x:a) : a
//SNIPPET_END: sig twice

//SNIPPET_START: def twice
let twice a f x = compose a a a f f x
//SNIPPET_END: def twice

//SNIPPET_START: implicit id applications
let _ : bool = id _ true
let _ : bool = id _ false
let _ : int = id _ (-1)
let _ : nat = id _ 17
let _ : string = id _ "hello"
let _ : int -> int = id _ (id _)
//SNIPPET_END: implicit id applications
