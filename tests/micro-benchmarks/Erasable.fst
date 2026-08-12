module Erasable

[@@erasable; expect_failure [162]] //must be marked noeq
type t0 =
  | This0 of int
  | That0 of bool

[@@erasable]
noeq
type t =
  | This of int
  | That of bool

[@@(expect_failure [34])]
let test0_fail (x:t) : Tot int =
  match x with
  | This i -> i
  | That _ -> 0

let test (x:t) : GTot int =
  match x with
  | This i -> i
  | That _ -> 0

[@@(expect_failure [34])]
let test1_fail (x:t{This? x}) : Tot int = This?._0 x
let test1 (x:t{This? x}) : GTot int = This?._0 x

let test_promotion (x:t) : Tot t =
  match x with
  | This i -> This (-i)
  | That b -> That (not b)

//this is illegal:
//erasable is only permitted inductive type definitions
[@@erasable; expect_failure [162]]
let e_nat = nat

(* GM: Note: e_nat_2 and e_nat_3 will appear
 * in Erasable.ml (as unit) since the definitions are erased
 * by the expect_failure, and we are left only with the vals *)

//erasable is permitted on type declarations
[@@erasable ]
val e_nat_2 : Type0
//but trying to instantiate that declaration with an non-inductive is illegal
[@@(expect_failure [162])]
let e_nat_2 = nat

//erasable is permitted on type declarations
[@@erasable ]
val e_nat_3 : Type0
//so long as these are then instantiated with noeq inductives
[@@(expect_failure [162])]
type e_nat_3 = | ENat3 of nat

//erasable is permitted on type declarations
[@@erasable]
val e_nat_4 : Type0
//so long as these are then instantiated with noeq inductives
[@@erasable]
noeq
type e_nat_4 = | ENat4 of nat

//erasable is permitted on type declarations
[@@erasable ]
val e_unit_5 : Type0
//and instantiating that declaration with a erasable type is okay
let e_unit_5 = t


(* Tests for extraction of erasable effects, combined with their lifts to non-erasable effects *)

type repr (a:Type) = a
let return (a:Type) (x:a) : repr a = x
let bind (a b:Type) (f:repr a) (g:a -> repr b) : repr b = g f
[@@ primitive_extraction]
total
effect {
  MPURE with {repr; return; bind}
}

//an erasable effect must be marked total
[@@ erasable; expect_failure [162]]
effect {
  MGHOST_not_total with {repr; return; bind}
}

[@@ erasable]
total
effect {
  MGHOST with {repr; return; bind}
}

let lift_PURE_MPURE (a:Type) (f:unit -> a) : repr a = f ()
sub_effect PURE ~> MPURE = lift_PURE_MPURE
sub_effect PURE ~> MGHOST = lift_PURE_MPURE

effect MPure (a:Type) = MPURE a
effect MGhost (a:Type) = MGHOST a

assume val f_mpure : unit -> MPure int
assume val f_mghost : unit -> MGhost int
assume val f_mghost_noninfo : unit -> MGhost (Ghost.erased int)

assume val f_ghost_noninfo : unit -> GTot (Ghost.erased int)
assume val f_ghost_info : unit -> GTot int

[@@ expect_failure [53]]
let eff_test0 () : MPure int =
  //cannot lift an erasable effect (GTot) to non-erasable effect (MPure) when the return type (int) is informative
  let x = f_ghost_info () in
  f_mpure ()

let eff_test1 () : MPure int =
  //lifting an erasable effect (GTot) to non-erasable effect (MPure) is ok,
  //as long as the return type of the erasable computation is non-informative (erased int)
  //the let binding for `y` is erased during extraction
  let y = f_ghost_noninfo () in
  f_mpure ()

//lifting an erasable effect (GTot) with informative type (int) to another erasable effect (MGhost) is ok
//note that this works even though we did not define a lift from GHOST to MGhost
//the typechecker implicitly promoted GHOST to PURE and then to MGhost
//the whole let binding goes away during extraction
let eff_test2 () : MGhost int = f_ghost_info () + 2

//as usual, the `n` argument will be extracted as a unit argument
let eff_test3 (n:Ghost.erased int) : MPure int =
  f_mpure () + 2

//the let binding for `x` gets erased, and eff_test3 is called with `()`
let eff_test4 () : MPure int =
  let y = f_mpure () in
  let x = f_ghost_noninfo () in
  eff_test3 x + y + 2

//erasure happens within match branches
let eff_test5 (b:bool) : MPure int =
  match b with
  | true -> eff_test4 ()
  | false ->
    eff_test3 (f_ghost_noninfo ()) + 2

//the let binding for `x` still gets erased
let eff_test6 (b:bool) : MPure int =
  let x =
    match b with
    | true -> f_ghost_noninfo ()
    | false -> Ghost.hide 4 in
  eff_test3 x

//so far we have tested lifting Ghost,
//now let's test lifting of MGHOST which is a user-defined erasable effect

effect {
  MDIV with {repr; return; bind}
}

effect MDiv (a:Type) = MDIV a

let lift_MGHOST_MDIV (a:Type) (f:repr a) : repr a = f
sub_effect MGHOST ~> MDIV = lift_MGHOST_MDIV

assume val f_mdiv : unit -> MDiv int

[@@ expect_failure [12]]
let eff_test7 () : MDiv int =
  //cannot lift an erasable effect (MGHOST) to non-erasable effect (MDIV) when the return type (int) is informative
  let x = f_mghost () in
  f_mdiv ()

//the let binding for `x` is erased at extraction time as expected
let eff_test7 () : MDiv int =
  let x = f_mghost_noninfo () in
  f_mdiv ()


(* Let's test GHOST and erasable effects with a new set of effects *)

total
effect {
  M1 with {repr; return; bind}
}

[@@erasable]
total
effect {
  M2 with {repr; return; bind}
}

sub_effect PURE ~> M1 = lift_PURE_MPURE
sub_effect PURE ~> M2 = lift_PURE_MPURE

assume val f_m1 : unit -> M1 int
assume val f_m2_info : unit -> M2 int
assume val f_m2_noninfo : unit -> M2 unit

//we can combine GHOST computation with M2, though we did not define a lift
//the typechecker implicitly promotes GHOST to PURE and then binds the computation
//the defn. is erased during extraction as usual
let eff_test8 () : M2 int =
  let x = f_m2_info () in
  let y = f_ghost_info () in
  x + y

//sequencing GHOST and M2 in the other order
//the defn. is erased during extraction as usual
let eff_test9 () : M2 int =
  let x = f_ghost_info () in
  let y = f_m2_info () in
  x + y

//M2 is erasable, so a GHOST computation can be promoted to it directly
let eff_test10 () : M2 int = f_ghost_info ()
