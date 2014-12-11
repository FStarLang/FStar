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


module HereditarySubstitutions

(* Simple types *)

type Ty =
  | O : Ty
  | A : dom:Ty -> codom:Ty -> Ty


(* De Bruijn contexts *)

type Con = list Ty


(* Variables *)

type Var =
  | Vz : Var
  | Vs : Var -> Var

val infer_var : Var -> Con -> Tot (option Ty)
let rec infer_var v g =
  match g with
    | [] -> None
    | a::g ->
       match v with
         | Vz -> Some a
         | Vs v -> infer_var v g

type typing_var v g a = infer_var v g = Some a


(* Removing a variable from a context *)

val rmv : g:Con -> a:Ty -> v:Var{typing_var v g a} -> Tot Con
let rec rmv g a v =
  match g with
    | b::g ->
       match v with
         | Vz -> g
         | Vs v -> b::(rmv g a v)

(* Conversely, adding a variable to a context (weakening) *)

val wkv : g:Con -> a:Ty -> b:Ty ->
          x:Var{typing_var x g a} -> y:Var{typing_var y (rmv g a x) b} ->
          Tot (z:Var{typing_var z g b})
let rec wkv g a b x y =
  match x with
    | Vz -> Vs y
    | Vs x ->
       match y with
         | Vz -> Vz
         | Vs y -> match g with | _::g -> Vs (wkv g a b x y)


(* Normal forms *)

type Nf =
  | NLam : Ty -> Nf -> Nf
  | NNeu : Ne -> Nf

and Ne =
  | NEApp : Var -> Sp -> Ne

and Sp =
  | SEmp : Ty -> Sp
  | SExt : Nf -> Sp -> Sp


val infer_nf : Nf -> Con -> Tot (option Ty)
val infer_ne : Ne -> Con -> Tot (option Ty)
val infer_sp : Sp -> Con -> Tot (option (Ty * Ty))

let rec infer_nf nf g =
  match nf with
    | NLam s nf ->
       (match infer_nf nf (s::g) with
          | Some t -> Some (A s t)
          | None -> None)
    | NNeu ne ->
       (match infer_ne ne g with
          | Some O -> Some O
          | _ -> None)

and infer_ne ne g =
  match ne with
    | NEApp x sp ->
       (match infer_var x g, infer_sp sp g with
          | Some s, Some (s', t) -> if s = s' then Some t else None
          | _, _ -> None)

and infer_sp sp g =
  match sp with
    | SEmp s -> Some (s, s)
    | SExt nf sp ->
       (match infer_nf nf g, infer_sp sp g with
          | Some t, Some (s, r) -> Some ((A t s), r)
          | _, _ -> None)

type typing_nf v g a = infer_nf v g = Some a
type typing_ne v g a = infer_ne v g = Some a
type typing_sp v g a b = infer_sp v g = Some (a,b)


(* Weakening normal forms *)

(* assume val wkSp : g:Con -> s:Ty -> t:Ty -> r:Ty -> *)
(*           x:Var{typing_var x g s} -> sp:Sp{typing_sp sp (rmv g s x) t r} -> *)
(*           Tot (sp:Sp{typing_sp sp g t r}) *)
(* val wkNf : g:Con -> s:Ty -> t:Ty -> *)
(*           x:Var{typing_var x g s} -> nf:Nf{typing_nf nf (rmv g s x) t} -> *)
(*           Tot (nf:Nf{typing_nf nf g t}) *)

(* let rec wkNf g s t x nf = *)
(*   match nf, t with *)
(*     | NLam _ u, A r t -> NLam r (wkNf (r::g) s t (Vs x) u) *)
(*     | NNeu (NEApp y us), O -> *)
(*        (match infer_var y (rmv g s x) with *)
(*           | Some t -> NNeu (NEApp (wkv g s t x y) (wkSp g s t O x us))) *)
