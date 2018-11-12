module Bug1368

assume val g : unit -> GTot bool

val test1 : unit -> Tot int
let test1 () =
    let x = (let y = g () in ()) in 42

val test2 : unit -> Tot int
let test2 () =
    let y = g () in
    let x = () in
    42
