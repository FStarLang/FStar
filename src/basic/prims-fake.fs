module Prims
open FSharp.Compatibility.OCaml
(* Needed to make bootstraping working (boot target of the Makefile);
   but when we actually type-check this within F*, we have the right
   definition of totality *)
type Tot<'a> = 'a
type int = bigint
type nat = int
type int' = int
type unit' = unit
type unit = unit'
type bool' = bool
type bool = bool'
type 'a option' = 'a option
type 'a option = 'a option'
type 'a list' = 'a list
type 'a list = 'a list'
let op_Multiply (x:int) (y:int) : int = x * y
let string_of_int x = string_of_int x
let string_of_bool b = string_of_bool b
let to_string x = x.ToString()
let parse_int = bigint.Parse
let parse_int32 = System.Int32.Parse
let of_int i = parse_int(string_of_int i)
let to_int i = parse_int32(to_string i)
