(** The [int] type and the various default operators. *)
type int      = Z.t
type nonzero  = int
let ( + )     = Z.add
let ( - )     = Z.sub
let ( * )     = Z.mul
let ( / )     = Z.ediv
let ( <= )    = Z.leq
let ( >= )    = Z.geq
let ( < )     = Z.lt
let ( > )     = Z.gt
let ( mod )   = Z.erem
let ( ~- )    = Z.neg
let abs       = Z.abs
let parse_int = Z.of_string
let to_string = Z.to_string

(** Some misc. types defined in Prims *)
type nonrec unit = unit
type nonrec bool = bool
type nonrec string = string
type nonrec 'a array = 'a array
type nonrec exn = exn
type nonrec 'a list = 'a list
type nonrec 'a option = 'a option

type _pos = int * int
type _rng = string * _pos * _pos
type range = _rng * _rng

type nat       = int
type pos       = int
type 'd b2t    = unit

type 'a squash = unit

type (' p, ' q) c_or =
  | Left of ' p
  | Right of ' q

type (' p, ' q) l_or = ('p, 'q) c_or squash

let uu___is_Left = function Left _ -> true | Right _ -> false

let uu___is_Right = function Left _ -> false | Right _ -> true

type (' p, ' q) c_and =
| And of ' p * ' q

type (' p, ' q) l_and = ('p, 'q) c_and squash

let uu___is_And _ = true


type c_True =
  | T

type l_True = c_True squash

let uu___is_T _ = true

type c_False = unit
(*This is how Coq extracts Inductive void := . Our extraction needs to be fixed to recognize when there
       are no constructors and generate this type abbreviation*)
type l_False = c_False squash

type (' p, ' q) l_imp = ('p -> 'q) squash

type (' p, ' q) l_iff = ((' p, ' q) l_imp, (' q, ' p) l_imp) l_and

type ' p l_not = (' p, l_False) l_imp

type (' a, ' p) l_Forall = unit

type (' a, ' p) l_Exists = unit


type (' p, ' q, 'dummyP) eq2 =  unit
type (' p, ' q, 'dummyP, 'dummyQ) eq3 =  unit

type prop     = Obj.t

type lex_t =
  | LexTop
  | LexCons of unit * Obj.t * lex_t
let (uu___is_LexTop : lex_t -> bool) =
  fun projectee  ->
    match projectee with | LexTop  -> true | uu____18 -> false

let (uu___is_LexCons : lex_t -> bool) =
  fun projectee  ->
    match projectee with | LexCons (a,_1,_2) -> true | uu____30 -> false

type 'Aprojectee __proj__LexCons__item__a = Obj.t
let (__proj__LexCons__item___1 :
  lex_t -> unit __proj__LexCons__item__a) =
  fun projectee  -> match projectee with | LexCons (a,_1,_2) -> _1
let (__proj__LexCons__item___2 : lex_t -> lex_t) =
  fun projectee  -> match projectee with | LexCons (a,_1,_2) -> _2

let cut = ()
let admit () = failwith "no admits"
let _assume () = ()
let _assert x = ()
let magic () = failwith "no magic"
let unsafe_coerce x = Obj.magic x
let op_Negation x = not x

let mk_range f a b c d : range = let r = (f, (a, b), (c, d)) in (r, r)
let range_0 : range = let z = parse_int "0" in mk_range "<dummy>" z z z z

(* These two cannot be (reasonably) implemented in extracted code *)
let range_of _ = range_0
let set_range_of x = x

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

let __proj__Cons__item__hd = List.hd

let __proj__Cons__item__tl = List.tl

let min = min

type ('a, 'b) admit = unit
