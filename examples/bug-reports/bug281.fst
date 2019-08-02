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
module Bug281

(* Test of substitution on big terms *)

open FStar.Classical
open FStar.StrongExcludedMiddle

type exp =
| EVar : nat -> exp
| EApp : exp -> exp -> exp
| ELam : exp -> exp

type sub = nat -> Tot (exp)

type renaming (s:sub) = (forall x. EVar? (s x))

val is_renaming : s:sub -> GTot nat
let is_renaming s =
  if (strong_excluded_middle (renaming s)) then 0 else 1

val is_evar : exp -> Tot nat
let is_evar e = if (EVar? e) then 0 else 1

val sub_einc : nat -> Tot (exp)
let sub_einc x = EVar (x+1)

val esubst : s:sub -> e:exp -> Tot (r:exp{renaming s /\ EVar? e ==> EVar? r})
(decreases %[is_evar e; is_renaming s; 1;e])
val sub_elam : s:sub -> Tot (r:sub{renaming s ==> renaming r})
(decreases %[1;is_renaming s; 0; EVar 0])

let rec sub_elam s =
let res : sub = fun x ->
if x = 0 then EVar 0 else esubst (sub_einc) (s (x-1))
in res
and esubst s e =
match e with
| EVar x -> s x
| EApp e1 e2 -> EApp (esubst s e1) (esubst s e2)
| ELam ebody -> ELam (esubst (sub_elam s) ebody)

let eesh = (esubst sub_einc)

let test f = EApp (EApp (EApp (eesh (eesh (eesh f))) (EVar 2)) (EVar 1)) (EVar 0)

val lemma : s:sub -> e:exp -> Lemma (esubst (sub_elam s) (eesh e)
                                   = eesh (esubst s e))
let lemma s e = admit()

(* Version without type : succeeds after a random time or fails *)
let plouf0 s f =lemma (sub_elam (sub_elam s)) (eesh (eesh f));
                lemma (sub_elam s) (eesh f);
                lemma (s) (f);
                assert(esubst (sub_elam (sub_elam (sub_elam s))) (test f) = test (esubst s f))

(* Succeeds after ~2-6sec *)
val plouf1 : s:sub -> f:exp -> Tot unit
let plouf1 s f =lemma (sub_elam (sub_elam s)) (eesh (eesh f));
                lemma (sub_elam s) (eesh f);
                lemma (s) (f);
                assert(esubst (sub_elam (sub_elam (sub_elam s))) (test f)
                     = test (esubst s f))

(* This takes around ~60 seconds to fail, or sometimes to succeed *)
val plouf2 : s:sub -> f :exp ->
  Lemma (esubst (sub_elam (sub_elam (sub_elam s))) (test f) = test (esubst s f))
let plouf2 s f =lemma (sub_elam (sub_elam s)) (eesh (eesh f));
                lemma (sub_elam s) (eesh f);
                lemma (s) (f)

(* another try, with raw encoding of the wp *)
val plouf4 : s:sub -> f:exp -> PURE unit (fun (p:pure_post unit) -> (esubst (sub_elam (sub_elam (sub_elam s))) (test f) = test (esubst s f)) ==> p ())
let plouf4 s f =lemma (sub_elam (sub_elam s)) (eesh (eesh f));
                lemma (sub_elam s) (eesh f);
                lemma (s) (f)
