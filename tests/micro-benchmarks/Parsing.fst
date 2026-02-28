module Parsing

(* Miscellaneous parsing tests, mostly about patterns
for now. *)

let foo (x,y : int & int) = x + y

// Currently parses (-1) as a pattern... odd but ok
val bar : (x:int{x == -1}) -> int
let bar - 1 = 2

type t = | A

let baz A = ()

type box t = | Box of t

let unbox (Box x) = x

let buz2 (Box x, Box y) = x + y

let buz1 (Box x) = x

let bub p =
  let (x, y) = p in
  x + y

let bub2 p =
  let x, y = p in
  x + y

let bab (x y : int {x >= y}) : nat = x - y

// Should fail and does
// val bab_box (Box x : box int) : nat
// Should fail and does
// val bab_box (Box x) : nat
// Should fail and does
// val bab_box : (Box x : int) -> nat

val bab_box (x y : box int {unbox x >= unbox y}) : nat
let bab_box (Box x) (Box y) : nat = x - y

// This should probably require parentheses,
// it looks really wrong.
let many_tuples   (x,y  z,w ) = x+y+z+w
let many_tuples_t (x,y  z,w : int & int) = x+y+z+w
// This would be nice
let many_tuples_ok   ((x,y) (z,w))             = x+y+z+w
let many_tuples_t_ok ((x,y) (z,w) : int & int) = x+y+z+w

val equality1 ($x : unit) : unit
let equality1 ($x : unit) : unit = ()

// Should parse, but fail
let test_eq_match (x : int) : int =
  match x with
  | $x -> x

// Should parse, but fail later
let test_eq_match2 (x : int) : int =
  match x with
  | $_ -> x

// Should work
val equality2 ($_ : unit) : unit
let equality2 ($_ : unit) : unit = ()

// Should not work? It parses and desugars, and then
// fails to infer the type of wildcard. It makes sense, just
// maybe nicer to fail earlier?
[@@expect_failure [66]]
val noparens _ : unit
