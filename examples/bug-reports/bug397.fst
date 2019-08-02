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
module Bug397

(* removing index also makes this work *)
type t (i:int) =
  | C : int -> t i

(* this works *)
let dummy2 (i:int) (s:t i)  =
  match s with
  | C _ -> 42

(* this fails *)
let dummy (i:int) (s:t i)  =
  match s, i with
  | C _, _ -> 42
