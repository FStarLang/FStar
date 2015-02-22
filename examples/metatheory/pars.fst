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

module ParallelSubstitution

open FunctionalExtensionality

(* Constructive-style progress and preservation proof for STLC with
   strong reduction, using deBruijn indices and parallel substitution. *)

type ty =
  | TArrow : t1:ty -> t2:ty -> ty

type var = nat

type exp =
  | EVar   : var -> exp
  | EApp   : exp -> exp -> exp
  | EAbs   : ty -> exp -> exp

val is_value : exp -> Tot bool
let is_value = is_EAbs

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
type renaming (s:sub) = (forall (x:var). is_EVar (s x))

assume val is_renaming : s:sub -> Tot (n:int{(renaming s ==> n=0) /\
                                             (~(renaming s) ==> n=1)})

val sub_inc : var -> Tot exp
let sub_inc y = EVar (y+1)

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if is_EVar e then 0 else 1


val subst : e:exp -> s:sub -> Pure exp (requires True)
                                       (ensures (fun e' -> renaming s /\ is_EVar e ==> is_EVar e'))
                                       (decreases %[is_var e; is_renaming s; e])
let rec subst e s =
  match e with
  | EVar x -> s x

  | EAbs t e1 ->
     let subst_eabs : y:var -> Tot (e:exp{renaming s ==> is_EVar e}) = fun y ->
       if y=0
       then EVar y
       else ((* renaming_sub_inc (); --unnecessary hint *)
             (* Why does the next recursive call terminate?
                1. If s is a renaming, we're done; since e is not a var, and s (y - 1) is, the lex ordering strictly decreases.
                2. If s is not a renaming, then since e is not a var, the first component of the lex order remains the same;
                   But, sub_inc is a renaming, so the second component decreases and we're done again.
              *)
             subst (s (y - 1)) sub_inc) in
     (* assert (renaming s ==> renaming subst_eabs); --unnecessary hint *)
     (* Why does the next recursive call terminate?
        1. If e1 is a var, we're done since e is not a var and so the first component decreases
        2. If not, e1 is a non-var proper sub-term of e; so the first component remains the same; the third component strictly decreases;
                   We have to show that the second comonent remains the same; i.e., subst_eabs is a renaming if s is a renaming.
                   Which we have done above.
      *)
     EAbs t (subst e1 subst_eabs)

  | EApp e1 e2 -> EApp (subst e1 s) (subst e2 s)

(*
   The above proof is nice, but you really want to use subst_eabs at the top-level.
   So, hoist it by hand ...
*)
val subst_eabs: s:sub -> Tot sub
let subst_eabs s y =
  if y = 0 then EVar y
  else subst (s (y-1)) sub_inc

val subst_extensional: e:exp -> s1:sub -> s2:sub{FEq s1 s2} ->
               Lemma (requires True) (ensures (subst e s1 = subst e s2))
                     [SMTPat (subst e s1);  SMTPat (subst e s2)]
let subst_extensional e s1 s2 = ()

let test_hoist (t:ty) (e:exp) (s:sub) =
  assert (subst (EAbs t e) s = EAbs t (subst e (subst_eabs s)))
