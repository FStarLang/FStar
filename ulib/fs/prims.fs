(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module Prims
open System.Numerics
module Obj = FSharp.Compatibility.OCaml.Obj

module Z = FSharp.Compatibility.OCaml.Big_int

(* Euclidean division and remainder:
   Inefficient implementation based on the naive version at
   https://en.wikipedia.org/wiki/Division_algorithm

   Note, in OCaml, we use ZArith's ediv and erem
*)
let rec ediv_rem (n:Z) (d:Z.big_int) : t * t =
    if Z.lt_big_int d Z.zero_big_int then
      let q, r = ediv_rem n (Z.minus_big_int d) in
      Z.minus_big_int q, r
    else if Z.lt_big_int n Z.zero_big_int then
      let q, r = ediv_rem (Z.minus_big_int n) d in
      if r = Z.zero_big_int then
        Z.minus_big_int q, Z.zero_big_int
      else
        Z.sub_big_int (Z.minus_big_int q) (Z.minus_big_int Z.unit_big_int),
        Z.sub_big_int d r
    else Z.quomod_big_int n d

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
let ( ~- ) (x:int) = (~-) x
let abs (x:int) = BigInteger.Abs x
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

type _pos = int * int
type _rng = string * _pos * _pos
type range = _rng * _rng

type nat       = int
type pos       = int
type 'd b2t    = B2t of unit

type 'a squash = Squash of unit

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

type (' a, ' p) l_Forall = L_forall of unit

type (' a, ' p) l_Exists = L_exists of unit


type (' p, ' q, 'dummyP) eq2 = Eq2 of unit
type (' p, ' q, 'dummyP, 'dummyQ) eq3 = Eq3 of unit

type prop     = obj

let cut = ()
let admit () = failwith "no admits"
let _assume () = ()
let _assert x = ()
let magic () = failwith "no magic"
let unsafe_coerce x = Obj.magic x
let op_Negation x = not x

let mk_range f a b c d : range = let r = (f, (a, b), (c, d)) in (r, r)
let range_0 = let z = parse_int "0" in mk_range "<dummy>" z z z z

(* These two cannot be (reasonably) implemented in extracted code *)
let range_of _ = ()
let set_range_of x = x

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
