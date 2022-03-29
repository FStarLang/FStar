﻿module Prims
open FSharp.Compatibility.OCaml
(* Needed to make bootstrapping work (boot target of the Makefile);
   but when we actually type-check this within F*, we have the right
   definition of totality *)
type Tot<'a> = 'a
type nat = int
type int' = int
type int = int'
type unit' = unit
type unit = unit'
type bool' = bool
type bool = bool'
type 'a option' = 'a option
type 'a option = 'a option'
type 'a list' = 'a list
type 'a list = 'a list'
let op_Multiply x y = x * y
let string_of_int x = string_of_int x
let string_of_bool b = string_of_bool b

type _pos = int * int
type _rng = string * _pos * _pos
type range = _rng * _rng
