module Erasable

[@erasable
 (expect_failure [162]) //must be marked noeq
]
type t0 =
  | This0 of int
  | That0 of bool

[@erasable]
noeq
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

//this is illegal:
//erasable is only permitted inductive type definitions
[@erasable
  (expect_failure [162])
]
let e_nat = nat

//erasable is permitted on type declarations
[@erasable ]
val e_nat_2 : Type0
//but trying to instantiate that declaration with an non-inductive is illegal
[@(expect_failure [162])]
let e_nat_2 = nat

//erasable is permitted on type declarations
[@erasable ]
val e_nat_3 : Type0
//so long as these are then instantiated with noeq inductives
[@(expect_failure [162])]
type e_nat_3 = | ENat3 of nat

//erasable is permitted on type declarations
[@erasable]
val e_nat_4 : Type0
//so long as these are then instantiated with noeq inductives
[@erasable]
noeq
type e_nat_4 = | ENat4 of nat
