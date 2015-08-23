#light "off"
module Prims
  type Tot<'a> = 'a
  type float' = float
  type float  = float'
  type uint8' = uint8
  type uint8 = uint8'
  type uint16' = uint16
  type uint16 = uint16'
  type int32 = int
  type nat = int
  type byte = Microsoft.FSharp.Core.byte
  type _exn = exn
  type exn = _exn
  type 'a list' = 'a list
  type 'a list = 'a list'
  type 'a option' = 'a option
  type 'a option = 'a option'
  type 'dummy b2t = Dummy_b2t of unit

  type (' p, ' q) l_or =
  | Left of ' p
  | Right of ' q

  let is_Left = function
    | Left _ -> true
    | _ -> false

  let is_Right = function
    | Right _ -> true
    | _ -> false

  type (' p, ' q) l_and =
  | And of ' p * ' q

  let is_And = function
    | And _ -> true

  type l__True =
    | T

  let is_T = function
    | T -> true

  type l__False = unit
  (*This is how Coq extracts Inductive void := . Our extraction needs to be fixed to recognize when there
    are no constructors and generate this type abbreviation*)

  type (' p, ' q) l_imp =
  ' p  ->  ' q

  type (' p, ' q) l_iff =
  ((' p, ' q) l_imp, (' q, ' p) l_imp) l_and

  type ' p l_not =
  (' p, l__False) l_imp

  type (' a, ' p) l__Forall =
  ' a  ->  ' p

  type ' f l__ForallTyp =
  unit  ->  ' f

  type (' a, ' p) l__Exists =
  | MkExists of ' a * ' p



  type heap = unit (*perhaps implement Heap concretely, and hence get it extracted fully automatically?
    We shoud get rid of this plethora of assumed primitives! *)
  type (' p, ' q, 'dummyP, 'dummyQ) l__Eq2 = Dummy_Eq2 of unit

  let ignore _ = ()
  let cut = ()
  let fst = fst
  let snd = snd
  let admit () = ()
  let _assume () = ()
  let _assert x = ()
  let magic () = failwith "no magic"
  let min x y = if x < y then x else y
  let op_Negation x = not x
  let op_Addition x y = x + y
  let op_Subtraction x y = x - y
  let op_Multiply x y = x * y
  let op_Division x y = x / y
  let op_Equality x y = x = y
  let op_disEquality x y = x<>y
  let op_AmpAmp x y = x && y
  let op_BarBar x y  = x || y
  let op_LessThanOrEqual x y = x <= y
  let op_GreaterThanOrEqual x y = x >= y
  let op_LessThan x y = x < y
  let op_GreaterThan x y = x > y
  let op_Modulus x y = x % y
  let is_Nil l = l = [] (*consider redefining List.isEmpty as this function*)
  let is_Cons l = not (is_Nil l)
