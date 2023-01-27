open Prims
type 'a cm =
  | CM of 'a * ('a -> 'a -> 'a) * unit * unit * unit 
let uu___is_CM : 'a . 'a cm -> Prims.bool = fun projectee -> true
let __proj__CM__item__unit : 'a . 'a cm -> 'a =
  fun projectee ->
    match projectee with
    | CM (unit, mult, identity, associativity, commutativity) -> unit
let __proj__CM__item__mult : 'a . 'a cm -> 'a -> 'a -> 'a =
  fun projectee ->
    match projectee with
    | CM (unit, mult, identity, associativity, commutativity) -> mult
let (int_plus_cm : Prims.int cm) = CM (Prims.int_zero, (+), (), (), ())
let (int_multiply_cm : Prims.int cm) = CM (Prims.int_one, ( * ), (), (), ())