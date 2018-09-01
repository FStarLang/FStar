module Test

let rec type_of_nat (n:nat) = bool

module D=Dep
let test (x:int) = D.create #(type_of_nat 0) 0 true

// type t =
//  | MkT : int -> t

// exception Foo of int
// // unfold
// // let f (x:int) = x

// // let g x = f x
