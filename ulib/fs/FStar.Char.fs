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
module FStar.Char
open Prims
//open FStar.Pervasives

type char = Prims.char

let lowercase = System.Char.ToLower
let uppercase = System.Char.ToUpper
let int_of_char (x:char) : int = Microsoft.FSharp.Core.Operators.int x |> System.Numerics.BigInteger.op_Implicit
let char_of_int (x:int) : char = Microsoft.FSharp.Core.Operators.int x |> Microsoft.FSharp.Core.Operators.char
