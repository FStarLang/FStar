module Bug188

val test : x:(option int){is_Some x} -> Tot int
let test x = (fun y -> Some.v y) x
