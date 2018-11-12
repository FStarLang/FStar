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
﻿module Prims
open FSharp.Compatibility.OCaml
(* Needed to make bootstraping working (boot target of the Makefile);
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
