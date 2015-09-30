module Bug 

(* Adding this line fixes the issue *)
//type bar (i:int) = int

val foo : (i:int & int)
let foo = (| 0, 0 |)
