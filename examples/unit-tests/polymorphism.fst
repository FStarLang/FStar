module Polymorphism

type foo 'a : Type => Type =
| Foo : 'b:Type => 'a -> 'b -> foo 'a 'b

let f x =
  match x with
  | Foo (_, y) -> y
