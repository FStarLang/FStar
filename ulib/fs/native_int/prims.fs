#light "off"
module Prims
  let down (x:obj) : 'b =
      x :?> 'b
  let lift (x:'a) : obj = x :> obj
  let checked_cast (x:'a) : 'b = lift x |> down
  type Tot<'a> = 'a
  type unit      = Microsoft.FSharp.Core.unit
  type bool      = Microsoft.FSharp.Core.bool
  type char      = Microsoft.FSharp.Core.char
  type string    = Microsoft.FSharp.Core.string
  type 'a array  = 'a Microsoft.FSharp.Core.array
  type double    = Microsoft.FSharp.Core.double
  type float     = Microsoft.FSharp.Core.float
  type int       = Microsoft.FSharp.Core.int
  type byte 	 = Microsoft.FSharp.Core.byte
  type exn       = Microsoft.FSharp.Core.exn
  type 'a list'  = 'a list
  type 'a list   = 'a list'
  type 'a option = 'a Microsoft.FSharp.Core.option
  type nat = int
  type 'dummy b2t = Dummy_b2t of unit
  type ('a,'b) l__HashMultiMap = ('a, 'b) Microsoft.FSharp.Collections.HashMultiMap
  type (' p, ' q) l_or =
  | Left of ' p
  | Right of ' q

  let uu___is_Left = function
    | Left _ -> true
    | _ -> false

  let uu___is_Right = function
    | Right _ -> true
    | _ -> false

  type (' p, ' q) l_and =
  | And of ' p * ' q

  let uu___is_And = function
    | And _ -> true

  type l__True =
    | T

  let uu___is_T = function
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
  let strcat x y = x ^ y
  let op_Negation x = not x

  open System.Numerics
  let ( + )  (x:int) (y:int) = x + y
  let ( - )  (x:int) (y:int) = x - y
  let ( * )  (x:int) (y:int) = x * y
  let ( / )  (x:int) (y:int) = x / y
  let ( <= ) (x:int) (y:int) = x <= y
  let ( >= ) (x:int) (y:int) = x >= y
  let ( < )  (x:int) (y:int) = x < y
  let ( > )  (x:int) (y:int) = x > y
  let ( % )  (x:int) (y:int) = x % y
  let parse_int = Integer.parse

  let op_Equality x y = x = y
  let op_disEquality x y = x<>y
  let op_AmpAmp x y = x && y
  let op_BarBar x y  = x || y
  let uu___is_Nil l = l = [] (*consider redefining List.isEmpty as this function*)
  let uu___is_Cons l = not (uu___is_Nil l)
  let raise e = raise e
  let string_of_bool b = sprintf "%b" b
  let string_of_int i = sprintf "%d" i
