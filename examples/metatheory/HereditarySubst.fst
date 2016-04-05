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


module HereditarySubst

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

val wkNf : g:Con -> s:Ty -> t:Ty ->
          x:Var{typing_var x g s} -> nf:Nf{typing_nf nf (rmv g s x) t} ->
          Tot (nf:Nf{typing_nf nf g t}) (decreases %[nf])
val wkSp : g:Con -> s:Ty -> t:Ty -> r:Ty ->
          x:Var{typing_var x g s} -> sp:Sp{typing_sp sp (rmv g s x) t r} ->
          Tot (sp:Sp{typing_sp sp g t r}) (decreases %[sp])

let rec wkNf g s t x nf =
  match nf, t with
    | NLam _ u, A r t -> NLam r (wkNf (r::g) s t (Vs x) u)
    | NNeu (NEApp y us), O ->
       (match infer_var y (rmv g s x) with
          | Some t -> NNeu (NEApp (wkv g s t x y) (wkSp g s t O x us)))

and wkSp g s t r x sp =
  match sp, t with
    | SEmp _, _ -> SEmp t
    | SExt u us, A t n -> SExt (wkNf g s t x u) (wkSp g s n r x us)


(* Equality between variables *)

type EqV =
  | Same : s:Ty -> EqV
  | Diff : y:Var -> EqV

val eq : g:Con -> s:Ty -> t:Ty -> x:Var{typing_var x g s} -> y:Var{typing_var y g t} -> Tot (r:EqV{(is_Diff r ==> typing_var (Diff.y r) (rmv g s x) t /\ y = wkv g s t x (Diff.y r)) /\ (is_Same r ==> (Same.s r = s) /\ (Same.s r = t) /\ (x = y))})
let rec eq g s t x y =
  match g with
    | a::g ->
       match x, y with
         | Vz, Vz -> Same s
         | Vz, Vs y -> Diff y
         | Vs x, Vz -> Diff Vz
         | Vs x, Vs y ->
            match eq g s t x y with
              | Same s -> Same s
              | Diff y -> Diff (Vs y)


(* Add a normal form at the end of a spine *)

val appSp : g:Con -> s:Ty -> t:Ty -> r:Ty -> sp:Sp{typing_sp sp g r (A s t)} -> u:Nf{typing_nf u g s} -> Tot (sp':Sp{typing_sp sp' g r t})
let rec appSp g s t r sp u =
  match sp, r with
    | SEmp (A _ t), _ -> SExt u (SEmp t)
    | SExt x xs, A _ n -> SExt x (appSp g s t n xs u)


(* η-expansion of normal forms *)

val nvar : g:Con -> s:Ty -> x:Var{typing_var x g s} -> Tot (nf:Nf{typing_nf nf g s}) (decreases %[s;1])
val ne2nf : g:Con -> s:Ty -> ne:Ne{typing_ne ne g s} -> Tot (nf:Nf{typing_nf nf g s}) (decreases %[s;0])

let rec nvar g s x = ne2nf g s (NEApp x (SEmp s))

and ne2nf g s xns =
  match s with
    | O -> NNeu xns
    | A s t ->
       match xns with
         | NEApp x ns ->
            match infer_var x g with
              | Some r -> NLam s (ne2nf (s::g) t (NEApp (Vs x) (appSp (s::g) s t r (wkSp (s::g) s r (A s t) Vz ns) (nvar (s::g) s Vz))))


(* Hereditary substitutions: substitute a variable by a normal form and
   normalize the result *)

val napp : g:Con -> t:Ty -> s:Ty -> f:Nf{typing_nf f g (A s t)} -> u:Nf{typing_nf u g s} -> Tot (fu:Nf{typing_nf fu g t}) (decreases %[s])
val substNf : g:Con -> s:Ty -> t:Ty -> a:Nf{typing_nf a g t} -> x:Var{typing_var x g s} -> b:Nf{typing_nf b (rmv g s x) s} -> Tot (c:Nf{typing_nf c (rmv g s x) t}) (decreases %[s;1;a])
val substSp : g:Con -> s:Ty -> t:Ty -> r:Ty -> a:Sp{typing_sp a g t r} -> x:Var{typing_var x g s} -> b:Nf{typing_nf b (rmv g s x) s} -> Tot (c:Sp{typing_sp c (rmv g s x) t r}) (decreases %[s;1;a])
val appNfSp : g:Con -> t:Ty -> s:Ty -> f:Nf{typing_nf f g s} -> sp:Sp{typing_sp sp g s t} -> Tot (c:Nf{typing_nf c g t}) (decreases %[s;0])

let rec napp g t s f u =
  match f with
    | NLam _ f -> substNf (s::g) s t f Vz u

and substNf g s t a x b =
  match t, a with
    | A r t, NLam _ a -> NLam r (substNf (r::g) s t a (Vs x) (wkNf (r::(rmv g s x)) r s Vz b))
    | O, NNeu (NEApp y ts) ->
       match infer_var y g with
         | Some t ->
            match eq g s t x y with
              | Same s -> appNfSp (rmv g s x) O s b (substSp g s s O ts x b)
              | Diff y -> NNeu (NEApp y (substSp g s t O ts x b))

and substSp g s t r a x b =
  match a with
    | SEmp t -> SEmp t
    | SExt c cs ->
       match t with
         | A t n -> SExt (substNf g s t c x b) (substSp g s n r cs x b)

and appNfSp g t s f sp =
  match sp with
    | SEmp _ -> f
    | SExt u us ->
       match s with
           | A r s -> appNfSp g t s (napp g s r f u) us


(* The whole set of terms *)

type Tm =
  | TVar : Var -> Tm
  | TLam : Ty -> Tm -> Tm
  | TApp : Tm -> Tm -> Tm

val infer_tm : Tm -> Con -> Tot (option Ty)
let rec infer_tm tm g =
  match tm with
    | TVar v -> infer_var v g
    | TLam a u ->
       (match infer_tm u (a::g) with
          | Some b -> Some (A a b)
          | None -> None)
    | TApp f u ->
       (match infer_tm f g, infer_tm u g with
          | Some (A a b), Some a' -> if a = a' then Some b else None
          | _, _ -> None)
type typing_tm t g a = infer_tm t g = Some a


(* The terms normalizer *)

val nf : g:Con -> s:Ty -> u:Tm{typing_tm u g s} -> Tot (n:Nf{typing_nf n g s})
                                                       (decreases %[u])
let rec nf g s u =
  match u, s with
    | TVar x, _ -> nvar g s x
    | TLam _ u, A s t -> NLam s (nf (s::g) t u)
    | TApp f u, _ ->
       (match infer_tm f g with
          | Some (A s t) -> napp g t s (nf g (A s t) f) (nf g s u))
