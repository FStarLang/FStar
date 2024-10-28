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
// This file needs --universes now

module Bug121

open FStar.FunctionalExtensionality

type var = nat

type exp =
  | EVar   : var -> exp
  | ELam   : exp -> exp

type sub = var -> Tot exp

type renaming (s:sub) = (forall (x:var). EVar? (s x))

assume val is_renaming : s:sub -> Tot (n:int{  (renaming s  ==> n=0) /\
                                      (~(renaming s) ==> n=1)})

val sub_inc : var -> Tot exp
let sub_inc y = EVar (y+1)

val renaming_sub_inc : unit -> Lemma (renaming (sub_inc))
let renaming_sub_inc _ = ()

let is_var (e:exp) : int = if EVar? e then 0 else 1

let rec subst (s:sub) (e:exp)
  : Pure exp (requires True)
    (ensures (fun e' -> (renaming s /\ EVar? e) ==> EVar? e'))
    (decreases %[is_var e; is_renaming s; 1 ; e])
= match e with
  | EVar x -> s x

  | ELam e1 ->
     let sub_elam = sub_lam s in
     ELam (subst sub_elam e1)
(* Does not work *)
(* and sub_lam (s:sub) (y:var) : Tot (e:exp{renaming s ==> EVar? e}) (decreases %[1 ; is_renaming s ; 0 ; ()])= *)
(*   if y=0 then EVar y *)
(*   else subst sub_inc (s (y-1)) *)
(* Works *)
and sub_lam (s:sub) : Tot (s':sub{renaming s ==> renaming s'}) (decreases %[1 ; is_renaming s ; 0 ; ()])=
  fun y ->
    if y=0 then EVar y
    else subst sub_inc (s (y-1))


(* Substitution extensional; trivial with the extensionality axiom *)
val subst_extensional: s1:sub -> s2:sub{feq s1 s2} -> e:exp ->
                        Lemma (requires True) (ensures (subst s1 e = subst s2 e))
                       (* [SMTPat (subst s1 e);  SMTPat (subst s2 e)] *)
let subst_extensional s1 s2 e = ()

(* This only works automatically with the patterns in
   subst_extensional above; it would be a lot cooler if this worked
   without, since that increases checking time.  Even worse, there is
   no way to prove this without the SMTPat (e.g. manually), or to use
   the SMTPat only locally, in this definition (`using` needed). *)
val sub_lam_hoist : e:exp -> s:sub -> Lemma (requires True)
      (ensures (subst s (ELam e) = ELam (subst (sub_lam s) e)))
let sub_lam_hoist e s = ()
