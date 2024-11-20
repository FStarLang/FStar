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
module Bug397b

open Platform.Bytes

type t (i:int) =
  | C of int

let bar (i:int) (s:t i) (d:int) (b:bytes)=
  C 1, 2

(* works *)
let foo2 (i:int) (s: t i) =
  bar i s 0

(* fails, but now error message is OK *)
let foo (i:int) (s: t i) =
  let b = createBytes 1 0uy in
  bar i s 0 b
