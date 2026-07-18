open Fstarcompiler
open Prims
type 'a equiv =
  | EQ of unit * unit * unit * unit 
let uu___is_EQ (projectee : 'a equiv) : Prims.bool= true
let equality_equiv (uu___ : unit) : 'a equiv= EQ ((), (), (), ())
type ('a, 'eq) cm =
  | CM of 'a * ('a -> 'a -> 'a) * unit * unit * unit * unit 
let uu___is_CM (eq : 'a equiv) (projectee : ('a, Obj.t) cm) : Prims.bool=
  true
let __proj__CM__item__unit (eq : 'a equiv) (projectee : ('a, Obj.t) cm) : 
  'a=
  match projectee with
  | CM (unit, mult, identity, associativity, commutativity, congruence) ->
      unit
let __proj__CM__item__mult (eq : 'a equiv) (projectee : ('a, Obj.t) cm) :
  'a -> 'a -> 'a=
  match projectee with
  | CM (unit, mult, identity, associativity, commutativity, congruence) ->
      mult
let int_plus_cm : (Prims.int, Obj.t) cm=
  CM (Prims.int_zero, (+), (), (), (), ())
let int_multiply_cm : (Prims.int, Obj.t) cm=
  CM (Prims.int_one, ( * ), (), (), (), ())
