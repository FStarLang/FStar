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


module HereditarySubstitutionsNat

(* Simple types *)

type Ty =
  | O : Ty
  | A : dom:Ty -> codom:Ty -> Ty


(* De Bruijn contexts *)

type Con = list Ty


(* Variables *)

type Var = nat

val infer_var : Var -> Con -> Tot (option Ty)
let rec infer_var v g =
  match g with
    | [] -> None
    | a::g -> if v = 0 then Some a else infer_var (v-1) g

type typing_var v g a = infer_var v g = Some a


(* Removing a variable from a context *)

(* val rmv : g:Con -> a:Ty -> v:Var{typing_var v g a} -> Tot Con *)
(* let rec rmv g a v = *)
(*   match g with *)
(*     | b::g -> if v = 0 then g else b::(rmv g a (v-1)) *)
