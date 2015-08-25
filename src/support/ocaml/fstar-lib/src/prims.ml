type unit'     = unit
type unit      = unit'

type bool'     = bool
type bool      = bool'

type char'     = char
type char      = char'

type string'   = string
type string    = string'

type int64'    = int64
type int64     = int64'

type 'a array' = 'a array
type 'a array  = 'a array'

type double'   = float
type double    = double'

type float'    = float
type float     = float'

type uint8'    = int
type uint8     = uint8'

type uint16'   = int
type uint16    = uint16'

type int32'    = int32
type int32     = int32'

type int'      = int
type int       = int'

type byte'     = char
type byte 	 = byte'

type exn'      = exn
type exn       = exn'

type 'a list'  = 'a list
type 'a list   = 'a list'

type 'a option' = 'a option
type 'a option  = 'a option'


type nat       = int
type 'd b2t    = unit

type (' p, ' q) l_or =
| Left of ' p
  | Right of ' q

let is_Left = (fun ( _discr_ ) -> (match (_discr_) with
					 | Left (_) -> begin
                                                   true
                                                 end
                                     | _ -> begin
				     false
				     end))

let is_Right = (fun ( _discr_ ) -> (match (_discr_) with
					  | Right (_) -> begin
                                                     true
                                                   end
                                      | _ -> begin
				      false
				      end))

type (' p, ' q) l_and =
| And of ' p * ' q
  let is_And _ = true

  type l__True =
    | T
let is_T _ = true

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


type (' p, ' q, 'dummyP, 'dummyQ) l__Eq2 =  unit
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
let op_Modulus x y = x mod y
let is_Nil l = l = [] (*consider redefining List.isEmpty as this function*)
let is_Cons l = not (is_Nil l)
let strcat x y = x ^ y
let is_Some = function (*consider redefining Option.isSome as this function*)
    | Some _ -> true
    | None -> false
let is_None o = not (is_Some o)
let raise e = raise e

