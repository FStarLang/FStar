module Test

val id : 'a -> Tot 'a 
let id x = x //the type argument is optimized away

let f (x:int) = id x

let g (x:int) = 
  let id' = fun (a:Type) (x:a) -> x in  //also here
  id' int x


let h (x:int) = (fun (a:Type) (x:a) -> x) int x //not here

