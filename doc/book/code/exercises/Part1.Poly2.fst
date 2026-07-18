module Part1.Poly2

//SNIPPET_START: id
let id (#a:Type) (x:a) : a = x
//SNIPPET_END: id

//SNIPPET_START: id applications
let _ : bool = id true
let _ : bool = id false
let _ : int = id (-1)
let _ : nat = id 17
let _ : string = id "hello"
let _ : int -> int = id id
//SNIPPET_END: id applications

//SNIPPET_START: explicit id applications
let _ = id #nat 0
let _ = id #(x:int{x == 0}) 0
let _ = id #(x:int{x <> 1}) 0
//SNIPPET_END: explicit id applications
