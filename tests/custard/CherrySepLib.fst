module CherrySepLib
open FStar.All
open FStar.Dyn
module IA = FStar.ImmutableArray

(* Separate compilation under Cherry (cherry.md, "Separate compilation"):
   the library half of CherrySepApp.  Every kind of counted value crosses the
   unit boundary in one direction or the other. *)

exception Oops of string

type shape = | Circle of int | Poly of list int

let rec mk (n: nat) : list int = if n = 0 then [] else n :: mk (n - 1)

(* Persistent globals, read from the other unit. *)
let g : list int = mk 3
let gd : dyn = mkdyn (Poly [7; 8])

let boom (s: string) : ML int = raise (Oops s)
let wrap (l: list int) : dyn = mkdyn l

(* Calls a closure built by the other unit, which may raise an exception
   this unit does not know. *)
let rec map (f: int -> ML int) (l: list int) : ML (list int) =
  match l with [] -> [] | x :: t -> f x :: map f t

let protect (f: unit -> ML string) : ML string =
  try f () with Oops m -> "caught " ^ m | e -> raise e

let adder (n: int) : int -> int = fun x -> x + n
let cell (l: list int) : ML (ref (list int)) = alloc l
let arr (l: list int) : IA.t int = IA.of_list l
let same (a b: shape) : bool = a = b

(* Borrow inference makes these parameters borrowed, and the interface says
   so (Syntax.CherryConv): the application keeps the values it passes. *)
let rec count (l: list int) : int = match l with [] -> 0 | x :: t -> x + count t
let rec append (l m: list int) : list int = match l with [] -> m | x :: t -> x :: append t m
(* Conventions from attributes, which the application must follow. *)
let keep ([@@@cherry_borrowed] l: list int) : list int = 0 :: l
let peek ([@@@cherry_owned] l: list int) : int = 1 + count l
