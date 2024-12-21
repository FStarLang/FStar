type int = Z.t[@printer Z.pp_print][@@deriving show]
let of_int = Z.of_int
let int_zero = Z.zero
let int_one = Z.one
let parse_int = Z.of_string
let to_string = Z.to_string

type tmp = string [@@deriving yojson]
let int_to_yojson x = tmp_to_yojson (to_string x)
let int_of_yojson x =
  match tmp_of_yojson x with
  | Ok x -> Ok (parse_int x)
  | Error x -> Error x

type attribute = unit
let (cps : attribute) = ()
type 'Auu____5 hasEq = unit
type eqtype = unit
type bool' = bool
[@@deriving yojson,show]
type bool = bool'
[@@deriving yojson,show]
type empty = unit
(*This is how Coq extracts Inductive void := . Our extraction needs to be fixed to recognize when there
       are no constructors and generate this type abbreviation*)
type trivial =
  | T
let (uu___is_T : trivial -> bool) = fun projectee  -> true
type nonrec unit = unit
type 'Ap squash = unit
type 'Ap auto_squash = unit
type l_True = unit
type l_False = unit
type ('Aa,'Ax,'dummyV0) equals =
  | Refl
let uu___is_Refl : 'Aa . 'Aa -> 'Aa -> ('Aa,unit,unit) equals -> bool =
  fun x  -> fun uu____65  -> fun projectee  -> true
type ('Aa,'Ax,'Ay) eq2 = unit
type ('Aa,'Ab,'Ax,'Ay) op_Equals_Equals_Equals = unit
type 'Ab b2t = unit
type ('Ap,'Aq) pair =
  | Pair of 'Ap * 'Aq
let uu___is_Pair : 'Ap 'Aq . ('Ap,'Aq) pair -> bool =
  fun projectee  -> true
let __proj__Pair__item___1 : 'Ap 'Aq . ('Ap,'Aq) pair -> 'Ap =
  fun projectee  -> match projectee with | Pair (_0,_1) -> _0
let __proj__Pair__item___2 : 'Ap 'Aq . ('Ap,'Aq) pair -> 'Aq =
  fun projectee  -> match projectee with | Pair (_0,_1) -> _1
type ('Ap,'Aq) l_and = unit
type ('Ap,'Aq) sum =
  | Left of 'Ap
  | Right of 'Aq
let uu___is_Left : 'Ap 'Aq . ('Ap,'Aq) sum -> bool =
  fun projectee  ->
    match projectee with | Left _0 -> true | uu____344 -> false

let __proj__Left__item___0 : 'Ap 'Aq . ('Ap,'Aq) sum -> 'Ap =
  fun projectee  -> match projectee with | Left _0 -> _0
let uu___is_Right : 'Ap 'Aq . ('Ap,'Aq) sum -> bool =
  fun projectee  ->
    match projectee with | Right _0 -> true | uu____404 -> false

let __proj__Right__item___0 : 'Ap 'Aq . ('Ap,'Aq) sum -> 'Aq =
  fun projectee  -> match projectee with | Right _0 -> _0
type ('Ap,'Aq) l_or = unit
type ('Ap,'Aq) l_imp = unit
type ('Ap,'Aq) l_iff = unit
type 'Ap l_not = unit
type ('Ap,'Aq,'Ar) l_ITE = unit
type ('Aa,'Ab,'Auu____484,'Auu____485) precedes = unit
type ('Aa,'Auu____490,'Auu____491) has_type = unit
type ('Aa,'Ap) l_Forall = unit
type prop = unit
let id x = x
type ('Aa,'Ab) dtuple2 =
  | Mkdtuple2 of 'Aa * 'Ab
let uu___is_Mkdtuple2 : 'Aa 'Ab . ('Aa,'Ab) dtuple2 -> bool =
  fun projectee  -> true
let __proj__Mkdtuple2__item___1 : 'Aa 'Ab . ('Aa,'Ab) dtuple2 -> 'Aa =
  fun projectee  -> match projectee with | Mkdtuple2 (_1,_2) -> _1
let __proj__Mkdtuple2__item___2 : 'Aa 'Ab . ('Aa,'Ab) dtuple2 -> 'Ab =
  fun projectee  -> match projectee with | Mkdtuple2 (_1,_2) -> _2
type ('Aa,'Ap) l_Exists = unit
type string' = string[@@deriving yojson,show]
type string = string'[@@deriving yojson,show]
type pure_pre = unit
type ('Aa,'Apre) pure_post' = unit
type 'Aa pure_post = unit
type 'Aa pure_wp = unit
type 'Auu____655 guard_free = unit
type ('Aa,'Ax,'Ap) pure_return = unit
type ('Ar1,'Aa,'Ab,'Awp1,'Awp2,'Ap) pure_bind_wp = 'Awp1
type ('Aa,'Ap,'Awp_then,'Awp_else,'Apost) pure_if_then_else = unit[@@deriving yojson,show]
type ('Aa,'Awp,'Apost) pure_ite_wp = unit
type ('Aa,'Awp1,'Awp2) pure_stronger = unit
type ('Aa,'Ab,'Awp,'Ap) pure_close_wp = unit
type ('Aa,'Aq,'Awp,'Ap) pure_assert_p = unit
type ('Aa,'Aq,'Awp,'Ap) pure_assume_p = unit
type ('Aa,'Ap) pure_null_wp = unit
type ('Aa,'Awp) pure_trivial = 'Awp
type ('Ap, 'Apost) pure_assert_wp = unit
type ('Aa,'Awp,'Auu____878) purewp_id = 'Awp


let op_AmpAmp x y = x && y
let op_BarBar x y  = x || y
let op_Negation x = not x

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

let op_Multiply x y = x * y
let op_Subtraction x y = x - y
let op_Addition x y = x + y
let op_Minus x = -x
let op_LessThan x y = x < y
let op_LessThanOrEqual x y = x <= y
let op_GreaterThan x y = x > y
let op_GreaterThanOrEqual x y = x >= y
let op_Equality x y = x = y
let op_disEquality x y = x<>y

type nonrec exn = exn
type 'a array' = 'a array[@@deriving yojson,show]
type 'a array = 'a array'[@@deriving yojson,show]
let strcat x y = x ^ y
let op_Hat x y = x ^ y

type 'a list' = 'a list[@@deriving yojson,show]
type 'a list = 'a list'[@@deriving yojson,show]
let uu___is_Nil : 'Aa . 'Aa list -> bool =
  fun projectee  -> match projectee with | []  -> true | uu____1190 -> false
let uu___is_Cons : 'Aa . 'Aa list -> bool =
  fun projectee  ->
    match projectee with | hd::tl -> true | uu____1216 -> false

let __proj__Cons__item__hd : 'Aa . 'Aa list -> 'Aa =
  fun projectee  -> match projectee with | hd::tl -> hd
let __proj__Cons__item__tl : 'Aa . 'Aa list -> 'Aa list =
  fun projectee  -> match projectee with | hd::tl -> tl
type pattern = unit


type ('Aa,'Auu____1278) decreases = unit
let returnM : 'Aa . 'Aa -> 'Aa = fun x  -> x
type lex_t =
  | LexTop
  | LexCons of unit * Obj.t * lex_t
let (uu___is_LexTop : lex_t -> bool) =
  fun projectee  ->
    match projectee with | LexTop  -> true | uu____1313 -> false

let (uu___is_LexCons : lex_t -> bool) =
  fun projectee  ->
    match projectee with | LexCons (a,_1,_2) -> true | uu____1327 -> false

type 'Aprojectee __proj__LexCons__item__a = Obj.t
let (__proj__LexCons__item___1 : lex_t -> Obj.t) =
  fun projectee  -> match projectee with | LexCons (a,_1,_2) -> _1
let (__proj__LexCons__item___2 : lex_t -> lex_t) =
  fun projectee  -> match projectee with | LexCons (a,_1,_2) -> _2
type ('Aa,'Awp) as_requires = 'Awp
type ('Aa,'Awp,'Ax) as_ensures = unit
let admit () = failwith "Prims.admit: cannot be executed"
let magic () = failwith "Prims.magic: cannot be executed"
let unsafe_coerce : 'Aa 'Ab . 'Aa -> 'Ab =
  fun x -> Obj.magic x

type 'Ap spinoff = 'Ap


type nat = int
type pos = int
type nonzero = int
let op_Modulus x y = x mod y
let op_Division x y = x / y
let rec (pow2 : nat -> pos) =
  fun x  ->
    Z.shift_left Z.one (Z.to_int x)

let (min : int -> int -> int) =
  fun x  -> fun y  -> if x <= y then x else y
let (abs : int -> int) =
  fun x  -> if x >= (parse_int "0") then x else op_Minus x
let string_of_bool = string_of_bool
let string_of_int = to_string
