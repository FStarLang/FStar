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
module Bug086

let x = 0

let xor = function
  | (0, 1)
  | (1, 0) -> 1
  | _ -> 0

val repr_bytes : nat -> Tot nat
let repr_bytes n =
     if n < 256 then 1
     else if n < 65536 then 2
     else if n < 16777216 then 3
     else if n < 4294967296 then 4
     else if n < 1099511627776 then 5
     else if n < 281474976710656 then 6
     else if n < 72057594037927936 then 7
     else 8

val f : unit -> GTot unit
let f () = ()

val repr_bytes2 : nat -> GTot nat
let repr_bytes2 n =
      let x = f () in
      if n < 256 then 1
      else if n < 65536 then 2
      else if n < 16777216 then 3
      else if n < 4294967296 then 4
      else if n < 1099511627776 then 5
      else if n < 281474976710656 then 6
      else if n < 72057594037927936 then 7
      else 8


val grepr_bytes : nat -> nat -> GTot nat
let grepr_bytes n _ =
      if n < 256 then 1
      else if n < 65536 then 2
      else if n < 16777216 then 3
      else if n < 4294967296 then 4
      else if n < 1099511627776 then 5
      else if n < 281474976710656 then 6
      else if n < 72057594037927936 then 7
      else 8
