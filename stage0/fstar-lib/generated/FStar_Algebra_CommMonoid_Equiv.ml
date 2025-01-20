open Prims
type 'a equiv =
  | EQ of unit * unit * unit * unit 
let uu___is_EQ : 'a . 'a equiv -> Prims.bool = fun projectee -> true
let equality_equiv : 'a . unit -> 'a equiv = fun uu___ -> EQ ((), (), (), ())
type ('a, 'eq) cm =
  | CM of 'a * ('a -> 'a -> 'a) * unit * unit * unit * unit 
let uu___is_CM : 'a . 'a equiv -> ('a, unit) cm -> Prims.bool =
  fun eq -> fun projectee -> true
let __proj__CM__item__unit : 'a . 'a equiv -> ('a, unit) cm -> 'a =
  fun eq ->
    fun projectee ->
      match projectee with
      | CM (unit, mult, identity, associativity, commutativity, congruence)
          -> unit
let __proj__CM__item__mult : 'a . 'a equiv -> ('a, unit) cm -> 'a -> 'a -> 'a
  =
  fun eq ->
    fun projectee ->
      match projectee with
      | CM (unit, mult, identity, associativity, commutativity, congruence)
          -> mult
let (int_plus_cm : (Prims.int, unit) cm) =
  CM (Prims.int_zero, (+), (), (), (), ())
let (int_multiply_cm : (Prims.int, unit) cm) =
  CM (Prims.int_one, ( * ), (), (), (), ())