module Prims
open System.Numerics

(* Euclidean division and remainder:
   Inefficient implementation based on the naive version at
   https://en.wikipedia.org/wiki/Division_algorithm

   Note, in OCaml, we use ZArith's ediv and erem
*)
let rec ediv_rem (n:bigint) (d:bigint) : bigint * bigint =
    if d < 0I then
      let q, r = ediv_rem n (-d) in
      -q, r
    else if n < 0I then
      let q, r = ediv_rem (-n) d in
      if r = 0I then
        -q, 0I
      else
        (-q) - (-1I),
        d - r
    else BigInteger.DivRem (n, d)

type int       = bigint
type nonzero = int
let ( + )  (x:bigint) (y:int) = x + y
let ( - )  (x:int) (y:int) = x - y
let ( * )  (x:int) (y:int) = x * y
let ( / )  (x:int) (y:int) = fst (ediv_rem x y)
let ( <= ) (x:int) (y:int)  = x <= y
let ( >= ) (x:int) (y:int)  = x >= y
let ( < )  (x:int) (y:int) = x < y
let ( > )  (x:int) (y:int) = x > y
let (mod) (x:int) (y:int)  = snd (ediv_rem x y)
let mod_f x y = x mod y
let ( ~- ) (x:int) = -x
let abs (x:int) = BigInteger.Abs x
let of_int (x:FSharp.Core.int) = BigInteger x
let int_zero = of_int 0
let int_one = of_int 1
let parse_int = BigInteger.Parse
let to_string (x:int) = x.ToString()

type unit      = Microsoft.FSharp.Core.unit
type bool      = Microsoft.FSharp.Core.bool
type string    = Microsoft.FSharp.Core.string
type 'a array  = 'a Microsoft.FSharp.Core.array
type exn       = Microsoft.FSharp.Core.exn
type 'a list'  = 'a list
type 'a list   = 'a Microsoft.FSharp.Collections.list

type nat       = int
type pos       = int
type b2t<'d>    = B2t of unit

type squash<'a> = Squash of unit

type sum<'p, 'q> =
  | Left of 'p
  | Right of 'q

type l_or<'p, 'q> = squash<sum<'p, 'q>>

let uu___is_Left x = match x with | Left _ -> true | Right _ -> false

let uu___is_Right x = match x with | Left _ -> false | Right _ -> true

type pair<'p, 'q> =
| Pair of 'p * 'q

type l_and<'p, 'q> = squash<pair<'p, 'q>>

let uu___is_Pair _ = true


type trivial =
  | T

type l_True = trivial squash

let uu___is_T _ = true

type empty = unit
(*This is how Coq extracts Inductive void := . Our extraction needs to be fixed to recognize when there
       are no constructors and generate this type abbreviation*)
type l_False = empty squash

type (' p, ' q) l_imp = ('p -> 'q) squash

type l_iff<'p, 'q> = l_and<l_imp<'p, 'q>, l_imp<'q, 'p>>

type ' p l_not = l_imp<'p, l_False>

type (' a, ' p) l_Forall = L_forall of unit

type (' a, ' p) l_Exists = L_exists of unit


type (' p, ' q, 'dummyP) eq2 = Eq2 of unit
type (' p, ' q, 'dummyP, 'dummyQ) op_Equals_Equals_Equals = Eq3 of unit

type prop     = obj

let cut = ()
let admit () = failwith "no admits"
let _assume () = ()
let _assert x = ()
let magic () = failwith "no magic"
let unsafe_coerce x = unbox (box x)
let not x = not x

let op_Equals x y = x = y
let op_Less_Greater x y = x<>y
let op_Amp_Amp x y = x && y
let op_Bar_Bar x y  = x || y
let uu___is_Nil l = l = [] (*consider redefining List.isEmpty as this function*)
let uu___is_Cons l = not (uu___is_Nil l)
let strcat x y = x ^ y

let string_of_bool (b:bool) = b.ToString()
let string_of_int (i:int) = i.ToString()

type ('a, 'b) dtuple2 =
  | Mkdtuple2 of 'a * 'b

let __proj__Mkdtuple2__item___1 x = match x with
  | Mkdtuple2 (x, _) -> x
let __proj__Mkdtuple2__item___2 x = match x with
  | Mkdtuple2 (_, x) -> x

let rec pow2 (n:int) = 
  if n = bigint 0 then
    bigint 1
  else
    (bigint 2) * pow2 (n - (bigint 1))

let __proj__Cons__item__tl x = match x with
  | _::tl -> tl
  | _     -> failwith "Impossible"

let min = min
