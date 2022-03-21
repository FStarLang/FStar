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
(* **********************
***       Types       ***
*************************)

module Bug060

type symbol_cat =
  | Tuple : symbol_cat
  | Constructor : list term -> term -> symbol_cat
  | Destructor : list term -> term -> symbol_cat

and symbol =
  {
    name : string;
    arity : nat;
    cat : symbol_cat
  }

and term =
  | Func : (symbol * list term) -> term
  | Name : string -> term

(* ***** List ******)

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _::q -> 1 + (length q)

(* *******************************
***        Predicates          ***
**********************************)

(*  Arity and arguments **)

type good_symbol = s:symbol{ match s.cat with
  | Tuple  -> true
  | Constructor list_arg _ -> length list_arg = s.arity
  | Destructor list_arg _ -> length list_arg = s.arity
  }

let n:term = Name "n"

(* Does type check *)
let a:good_symbol =
  let x = { name = "enc" ; arity = 2; cat = Constructor [n;n] n } in
  x

(*  Does not type check *)
let a':good_symbol = { name = "enc" ; arity = 2; cat = Constructor [n;n] n }
(* *)


let pair : (x:nat & y:nat{y > x}) =
    let z = (|0, 1|) in
    z

let pair2 : (x:nat & y:nat{y > x}) = (|0, 1|)
