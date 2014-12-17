(*
   Copyright 2014 Chantal Keller and Microsoft Research

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


module HereditarySubstitutionsDT


(* Simple types *)

type Ty =
  | O : Ty
  | A : dom:Ty -> codom:Ty -> Ty


(* De Bruijn contexts *)

type Con = list Ty


(* Variables *)

type Var : Con -> Ty -> Type =
  | Vz : g:Con -> a:Ty -> Var (a::g) a
  | Vs : g:Con -> a:Ty -> b:Ty -> Var g a -> Var (b::g) a


(* Removing a variable from a context *)

val rmv : g:Con -> a:Ty -> v:Var g a -> Tot Con
let rec rmv g a v =
  match v with
    | Vz d b -> d
    | Vs d b c x -> c::(rmv d b x)


(* Conversely, adding a variable to a context (weakening) *)

(* val wkv : g:Con -> s:Ty -> t:Ty -> x:Var g s -> Var (rmv g s x) t -> Var g t *)
(* let rec wkv g s t x y = *)
(*   match x with *)
(*     | Vz g _ -> Vs g t s y *)
(*     | Vs g _ r x -> *)
(*        match y with *)
(*          | Vz _ _ -> Vz g t *)
(*          | Vs _ _ _ y -> Vs g t r (wkv g s t x y) *)
