(*
   Copyright 2008-2014 Catalin Hritcu, Nikhil Swamy, Microsoft Research and Inria

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

module ParSubst

open FStar.FunctionalExtensionality

(* Parallel substitution, with comments
  (the real development is in ) *)

type ty =
  | TArrow : t1:ty -> t2:ty -> ty

type var = nat

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : ty -> exp -> exp

val is_value : exp -> Tot bool
let is_value = EAbs?

(* Parallel substitution operation `subst` *)

(* The termination argument uses a lexicographic ordering composed of:
   0) a bit saying whether the expression is a variable or not;
   1) an _undecidable_ well-founded order on substitutions that
      equates all renamings, equates all non-renamings, and makes
      renamings strictly smaller than non-renamings; we write down a
      non-constructive function mapping substitutions (infinite
      objects) to 0 (renaming) or 1 (non-renaming)
   2) the structure of the expression e *)

(* My proposal would be to put this in Classic not Tot *)
(* assume val excluded_middle : p:Type -> Tot (b:bool{b = true <==> p}) *)

type sub = var -> Tot exp
type renaming (s:sub) = (forall (x:var). EVar? (s x))

assume val is_renaming : s:sub -> Tot (n:int{(renaming s ==> n=0) /\
                                             (~(renaming s) ==> n=1)})

val sub_inc : var -> Tot exp
let sub_inc y = EVar (y+1)

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if EVar? e then 0 else 1


val subst_eabs: s:sub -> y:var -> Tot (e:exp{renaming s ==> EVar? e})
                                    (decreases %[1;is_renaming s; 0; EVar 0])

val subst : e:exp -> s:sub -> Pure exp (requires True)
                                       (ensures (fun e' -> renaming s /\ EVar? e ==> EVar? e'))
                                       (decreases %[is_var e; is_renaming s; 1; e])
let rec subst e s =
  match e with
  | EVar x -> s x

  | EAbs t e1 ->
     EAbs t (subst e1 (subst_eabs s))

  | EApp e1 e2 -> EApp (subst e1 s) (subst e2 s)

and subst_eabs s y =
  if y = 0 then EVar y
  else subst (s (y-1)) sub_inc

val subst_extensional: e:exp -> s1:sub -> s2:sub{feq s1 s2} ->
               Lemma (requires True) (ensures (subst e s1 = subst e s2))
                     [SMTPat (subst e s1);  SMTPat (subst e s2)]
let rec subst_extensional e s1 s2 =
  let open FStar.Tactics in
  match e with
  | EVar _ -> ()
  | EAbs t e1 ->
    assert (subst (EAbs t e1) s1 == EAbs t (subst e1 (subst_eabs s1)))
      by norm [delta_only [`%subst]];
    assert (subst (EAbs t e1) s2 == EAbs t (subst e1 (subst_eabs s2)))
      by norm [delta_only [`%subst]];
    subst_extensional e1 (subst_eabs s1) (subst_eabs s2)
  | EApp e1 e2 -> subst_extensional e1 s1 s2; subst_extensional e2 s1 s2

let test_hoist (t:ty) (e:exp) (s:sub) =
  assert (subst (EAbs t e) s = EAbs t (subst e (subst_eabs s)))
