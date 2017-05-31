(** The [int] type and the various default operators. *)
type int      = Big_int_Z.big_int
type nonzero  = int
let ( + )     = Big_int_Z.add_big_int
let ( - )     = Big_int_Z.sub_big_int
let ( * )     = Big_int_Z.mult_big_int
let ( / )     = Big_int_Z.div_big_int
let ( <= )    = Big_int_Z.le_big_int
let ( >= )    = Big_int_Z.ge_big_int
let ( < )     = Big_int_Z.lt_big_int
let ( > )     = Big_int_Z.gt_big_int
let ( mod )   = Big_int_Z.mod_big_int
let ( ~- )    = Big_int_Z.minus_big_int
let abs       = Big_int_Z.abs_big_int
let parse_int = Big_int_Z.big_int_of_string
let to_string = Big_int_Z.string_of_big_int

(** Some misc. types defined in Prims *)
type nonrec unit = unit
type nonrec bool = bool
type nonrec string = string
type nonrec 'a array = 'a array
type nonrec exn = exn
type nonrec 'a list = 'a list
type nonrec 'a option = 'a option

type range     = unit
type nat       = int
type pos       = int
type 'd b2t    = unit

type (' p, ' q) c_or =
  | Left of ' p
  | Right of ' q

type (' p, ' q) l_or = (' p, ' q) c_or

let uu___is_Left = function Left _ -> true | Right _ -> false

let uu___is_Right = function Left _ -> false | Right _ -> true

type (' p, ' q) c_and =
| And of ' p * ' q

type (' p, ' q) l_and = (' p, ' q) c_and

let uu___is_And _ = true

type l_True =
  | T

let uu___is_T _ = true

type l_False = unit
(*This is how Coq extracts Inductive void := . Our extraction needs to be fixed to recognize when there
       are no constructors and generate this type abbreviation*)

type (' p, ' q) l_imp = ' p  ->  ' q

type (' p, ' q) l_iff = ((' p, ' q) l_imp, (' q, ' p) l_imp) l_and

type ' p l_not = (' p, l_False) l_imp

type (' a, ' p) l_Forall = unit

type (' a, ' p) l_Exists = unit


type (' p, ' q, 'dummyP) eq2 =  unit
type (' p, ' q, 'dummyP, 'dummyQ) eq3 =  unit

type prop     = Obj.t

let cut = ()
let admit () = failwith "no admits"
let _assume () = ()
let _assert x = ()
let magic () = failwith "no magic"
let unsafe_coerce x = Obj.magic x
let op_Negation x = not x

(* for partially variants of the operators *)
let op_Multiply x y = x * y
let op_Subtraction x y = x - y
let op_Addition x y = x + y
let op_LessThanOrEqual x y = x <= y
let op_LessThan x y = x < y
let op_GreaterThanOrEqual x y = x >= y
let op_GreaterThan x y = x > y

let op_Equality x y = x = y
let op_disEquality x y = x<>y
let op_AmpAmp x y = x && y
let op_BarBar x y  = x || y
let uu___is_Nil l = l = [] (*consider redefining List.isEmpty as this function*)
let uu___is_Cons l = not (uu___is_Nil l)
let strcat x y = x ^ y

let string_of_bool = string_of_bool
let string_of_int = to_string

type ('a, 'b) dtuple2 =
  | Mkdtuple2 of 'a * 'b

let __proj__Mkdtuple2__item___1 x = match x with
  | Mkdtuple2 (x, _) -> x
let __proj__Mkdtuple2__item___2 x = match x with
  | Mkdtuple2 (_, x) -> x

let rec pow2 n =
  let open Z in
  if n = ~$0 then
    ~$1
  else
    ~$2 * pow2 (n - ~$1)

let __proj__Cons__item__tl = function
  | _::tl -> tl
  | _     -> failwith "Impossible"

let min = min
