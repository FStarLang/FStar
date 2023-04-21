#light "off"
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
type 'a option = 'a Microsoft.FSharp.Core.option

type nat       = int
type pos       = int
type 'd b2t    = B2t of unit

type 'a squash = Squash of unit

type (' p, ' q) sum =
  | Left of ' p
  | Right of ' q

type (' p, ' q) l_or = ('p, 'q) sum squash

let uu___is_Left = function Left _ -> true | Right _ -> false

let uu___is_Right = function Left _ -> false | Right _ -> true

type (' p, ' q) pair =
| Pair of ' p * ' q

type (' p, ' q) l_and = ('p, 'q) pair squash

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

type (' p, ' q) l_iff = ((' p, ' q) l_imp, (' q, ' p) l_imp) l_and

type ' p l_not = (' p, l_False) l_imp

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
let op_Negation x = not x

let op_Equality x y = x = y
let op_disEquality x y = x<>y
let op_AmpAmp x y = x && y
let op_BarBar x y  = x || y
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

let rec pow2 (n:int) = if n = bigint 0 then
                      bigint 1
                   else
                      (bigint 2) * pow2 (n - (bigint 1))

let __proj__Cons__item__tl = function
  | _::tl -> tl
  | _     -> failwith "Impossible"

let min = min
