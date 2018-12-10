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
module Eta_expand

open FStar.All

type t =
  | A
  | B

let dec: t -> Type0 = function
  | A -> int
  | B -> bool

let fun_a (x: int) (s: int): int = x
let fun_b (x: bool) (s: int): bool = x

let choose: a:t -> dec a -> int -> dec a = function
  | A -> fun_a
  | B -> fun_b

(* One recurring bug has been shadowing of variables when a function is eta-expanded two or
   more times during extraction. If this is the case, x will be 2 when executing the OCaml code *)
let _ =
  match (choose A 0 2) with
  | 0 -> () (* correct behaviour *)
  | 2 -> failwith "Failure of eta-expansion in FStar.Extraction.ML.Term"
  | _ -> failwith "Unknown failure"
