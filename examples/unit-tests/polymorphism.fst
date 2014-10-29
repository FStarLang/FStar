module Polymorphism

(* val test : int * unit *)
(* let test = let g x = x in (g 3, g ()) *)

type foo 'a : Type => Type =
| Foo : 'b:Type => 'a -> 'b -> foo 'a 'b

let f x =
  match x with
  | Foo (_, y) -> y

(* val test2 : int * unit *)
(* let test2 = (3, ()) *)
