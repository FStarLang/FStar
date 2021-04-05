module Bug1604

type t = | A : int -> int -> t

assume val f : int -> int -> int

assume val g : bool -> int -> int -> int

let test1 : int = 1 `f` 2
let test2 : t = 3 `A` 4
let test3 : int = 5 `(g true)` 6
let test4 : int = 7 `g true` 8

let test5 a c e = a `f` c `g true` e

let test6 a c e =
    assert (test5 a c e == g true (f a c) e)

type infix = | Infix: int -> int -> infix
let ff x y = x `Infix` y

assume val foo: int -> int -> int -> bool
let gg x y z = y `foo x` z
