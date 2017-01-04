module Bug188

val test0 : x:(option int){Some? x} -> Tot int
let test0 x = (fun (y:_{Some? y}) -> Some?.v y) x // Works

val test : x:(option int){Some? x} -> Tot int
let test x = (fun y -> Some?.v y) x // Fails
