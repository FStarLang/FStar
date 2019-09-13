module Erasable

[@erasable]
type t =
  | This of int
  | That of bool

[@(expect_failure [34])]
let test0_fail (x:t) : Tot int =
  match x with
  | This i -> i
  | That _ -> 0

let test (x:t) : GTot int =
  match x with
  | This i -> i
  | That _ -> 0

[@(expect_failure [34])]
let test1_fail (x:t{This? x}) : Tot int = This?._0 x
let test1 (x:t{This? x}) : GTot int = This?._0 x

let test_promotion (x:t) : Tot t =
  match x with
  | This i -> This (-i)
  | That b -> That (not b)
