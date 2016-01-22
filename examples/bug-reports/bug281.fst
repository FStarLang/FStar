(*--build-config
    options:--z3timeout 20 --max_fuel 8 --max_ifuel 6 --initial_fuel 4 --initial_ifuel 2  --log_types --logQueries;
    other-files:../../lib/FStar.Classical.fst
  --*)
module Test

(* Test of substitution on big terms *)

open Classical

type exp =
| EVar : nat -> exp
| EApp : exp -> exp -> exp 
| ELam : exp -> exp 

type sub = nat -> Tot (exp)

type renaming (s:sub) = (forall x. is_EVar (s x))

val is_renaming : s:sub -> Tot nat
let is_renaming s =
  if (excluded_middle (renaming s)) then 0 else 1

val is_evar : exp -> Tot nat
let is_evar e = if (is_EVar e) then 0 else 1

val sub_einc : nat -> Tot (exp)
let sub_einc x = EVar (x+1)

val esubst : s:sub -> e:exp -> Tot (r:exp{renaming s /\ is_EVar e ==> is_EVar r})
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

(* Succeeds after ~2-6sec
opaque val plouf1 : s:sub -> f:exp -> Tot unit
let plouf1 s f =lemma (sub_elam (sub_elam s)) (eesh (eesh f));
                lemma (sub_elam s) (eesh f);
                lemma (s) (f);
                assert(esubst (sub_elam (sub_elam (sub_elam s))) (test f)
                     = test (esubst s f))
*)

(* This takes around ~60 seconds to fail, or sometimes to succeed *)
val plouf2 : s:sub -> f :exp ->
  Lemma (esubst (sub_elam (sub_elam (sub_elam s))) (test f) = test (esubst s f))
let plouf2 s f =lemma (sub_elam (sub_elam s)) (eesh (eesh f));
                lemma (sub_elam s) (eesh f);
                lemma (s) (f)
