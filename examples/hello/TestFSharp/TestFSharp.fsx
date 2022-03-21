#r "../../../bin/ulibfs.dll"
#r "bin/Debug/TestFSharp.dll"

open TestFSharp

let a = pass () () (fun x y -> x = y)
let b = pass 5 2 (fun x y -> x = y)

// TODO: 
//let b = fail () () () () (fun x y -> x = y)
