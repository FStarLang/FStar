open Prims
type 'a cm =
  | CM of 'a * ('a -> 'a -> 'a) * unit * unit * unit 
let uu___is_CM (projectee : 'a cm) : Prims.bool= true
let __proj__CM__item__unit (projectee : 'a cm) : 'a=
  match projectee with
  | CM (unit, mult, identity, associativity, commutativity) -> unit
let __proj__CM__item__mult (projectee : 'a cm) : 'a -> 'a -> 'a=
  match projectee with
  | CM (unit, mult, identity, associativity, commutativity) -> mult
let int_plus_cm : Prims.int cm= CM (Prims.int_zero, (+), (), (), ())
let int_multiply_cm : Prims.int cm= CM (Prims.int_one, ( * ), (), (), ())
