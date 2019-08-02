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
module StlcCbvDbPntSubstLists

(* de Bruijn indices based STLC *)

type typ =
  | TBool
  | TArrow: typ -> typ -> typ

type exp =
  | EVar: nat -> exp        (* de Bruijn index *)
  | EAbs: typ -> exp -> exp (* no names *)
  | EApp: exp -> exp -> exp

(* returns true if the expression contains a (CH: top-level) free 0 *)
val free_zero: exp -> Tot bool
let rec free_zero e =
  match e with
  | EVar k     -> k = 0
  | EAbs _ _   -> false (* CH: I find it surprising that you're not
                               searching for a 1 inside the body;
                               this function only makes sense in shift _ _ -1, right?
			   AR: Yes, that's right. The indices are type nat, and so,
			       when shifting with -1, we need to show that there are
			       no free top level zeros. The general case of looking up
			       0 as free variable, where we would look for 1 inside a
			       lambda, is covered by free_in (these fns
			       could have some better names).
			*)
  | EApp e1 e2 -> free_zero e1 || free_zero e2

(*
 * d is the number of units shifted by, c is the number of seen binders
 * since d can be -1, refinement ensures that indices remain nats
 *)
val shift: e:exp -> c:nat ->
           d:int{d >= -1 /\ (d = -1 ==> (not (free_zero e) \/ c > 0))}
           -> Tot exp (decreases e)
let rec shift e c d = match e with
  | EVar k       -> if k < c then EVar k else EVar (k + d)
  | EAbs t e1    -> EAbs t (shift e1 (c + 1) d)
  | EApp e1 e2   -> EApp (shift e1 c d) (shift e2 c d)

(* consecutive shifts can add up the units *)
val consec_shifts_lem: e:exp -> c:nat -> d1:nat -> d2:nat ->
                       Lemma (requires True) (ensures (shift (shift e c d1) c d2 = shift e c (d1 + d2)))
let rec consec_shifts_lem e c d1 d2 = match e with
  | EVar _     -> ()
  | EAbs _ e1  -> consec_shifts_lem e1 (c + 1) d1 d2
  | EApp e1 e2 -> consec_shifts_lem e1 c d1 d2; consec_shifts_lem e2 c d1 d2

(* [j |-> e'] e *)
val substitute: e:exp -> j:nat -> e':exp -> Tot exp (decreases e)
let rec substitute e j e' = match e with
  | EVar k       -> if j = k then e' else EVar k
  | EAbs t e1    -> EAbs t (substitute e1 (j + 1) (shift e' 0 1))
  | EApp e1 e2   -> EApp (substitute e1 j e') (substitute e2 j e')

val subst_zero_lem: e1:exp -> e2:exp{not (free_zero e2)} ->
                    Lemma (requires True)
                          (ensures (not (free_zero (substitute e1 0 e2)))) (decreases e1) [SMTPat (substitute e1 0 e2)]
let rec subst_zero_lem e1 e2 = match e1 with
  | EVar k       -> ()
  | EAbs _ _     -> ()
  | EApp e1' e2' -> (subst_zero_lem e1' e2; subst_zero_lem e2' e2)

val is_value: exp -> Tot bool
let is_value = EAbs?

val step: exp -> Tot (option exp)
let rec step = function
  | EApp e1 e2 ->
     if is_value e1 then
       if is_value e2 then
	 (match e1 with
	  | EAbs _ e1' -> Some (shift (substitute e1' 0 (shift e2 0 1)) 0 (-1)))
       else
	 (match step e2 with
	  | None     -> None
	  | Some e2' -> Some (EApp e1 e2'))
     else
       (match step e1 with
	| None     -> None
	| Some e1' -> Some (EApp e1' e2))
  | _ -> None

type env = list typ

let lookup = List.Tot.nth

val typing: g:env -> e:exp -> Tot (option typ) (decreases e)
let rec typing g e = match e with
  | EVar k   -> lookup g k
  | EAbs t1 e1 ->
     (match typing (t1::g) e1 with
      | None -> None
      | Some t2 -> Some (TArrow t1 t2))
  | EApp e1 e2 ->
     match (typing g e1, typing g e2) with
     | Some (TArrow t1 t2), Some t1' -> if t1 = t1' then Some t2 else None
     | _, _ -> None

val progress: e:exp{Some? (typing [] e)} ->
              Lemma (requires True) (ensures (is_value e \/ Some? (step e)))
let rec progress e =
  match e with
  | EApp e1 e2 -> progress e1; progress e2
  | EAbs t e1 -> ()

let len = List.Tot.length

let app_len = List.Tot.append_length

let app_nil = List.Tot.append_l_nil

let list_assoc = List.Tot.append_assoc

(* g' @ (t::g) = (g' @ [t]) @ g /\ lookup (g' @ (t::g)) (len g') = t *)
val list_assoc_a: g:env -> g':env -> t:typ -> Lemma (requires True) (ensures ((g' @ (t::g)) = ((g' @ [t]) @ g) /\
                                                                              lookup (g' @ (t::g)) (len g') = Some t)) (decreases g')
let rec list_assoc_a g g' t = match g' with
  | []     -> ()
  | hd::tl -> list_assoc_a g tl t

(* t1'::(g' @ (t::g)) = (t1'::g') @ (t::g) *)
val list_assoc_b: g:env -> g':env -> t1':typ -> t:typ -> Lemma (requires True) (ensures ((t1'::(g' @ (t::g))) = ((t1'::g') @ (t::g))))
let list_assoc_b g g' t1' t = ()

(* inversion for lookup, lookup for indices less than length of env succeeds *)
val lookup_inv: g:env -> n:nat -> Lemma (requires True) (ensures (if n < len g then Some? (lookup g n) else None? (lookup g n))) [SMTPat (lookup g n)]
let rec lookup_inv g n = match g with
  | []    -> ()
  | _::tl -> if n = 0 then () else lookup_inv tl (n - 1)

(* inversion for lookup in app, lookup in g' @ g means either lookup in g' or in g *)
val lookup_app_inv: g:env -> g':env -> k:nat{Some? (lookup (g' @ g) k)} -> Lemma (requires (True))
                   (ensures ((k < len g' /\ lookup (g' @ g) k = lookup g' k) \/ (k >= len g' /\ lookup (g' @ g) k = lookup g (k - len g'))))
                   [SMTPat (lookup (g' @ g) k)]
let rec lookup_app_inv g g' k = match g' with
  | []     -> ()
  | hd::tl -> if k = 0 then () else lookup_app_inv g tl (k - 1)

(* lookup g k ==> lookup (g' @ g) (k + len g') *)
val lookup_ext_f: g:env -> n:nat{Some? (lookup g n)} -> g':env ->
                  Lemma (requires True) (ensures (Some? (lookup (g' @ g) (n + len g')) /\
                                                  Some?.v  (lookup (g' @ g) (n + len g')) = Some?.v (lookup g n)))
                  (decreases g')
let rec lookup_ext_f g n g' = match g' with
  | []    -> ()
  | _::tl -> lookup_ext_f g n tl

(* if g' @ g |- e : t then g' @ g'' @ g |- (shift e (len g') (len g'')) : t *)
val weakening: g:env -> g':env -> g'':env -> e:exp{Some? (typing (g' @ g) e)} ->
               Lemma (requires True) (ensures (Some? (typing (g' @ (g'' @ g)) (shift e (len g') (len g''))) /\
                                               Some?.v (typing (g' @ (g'' @ g)) (shift e (len g') (len g''))) = Some?.v (typing (g' @ g) e))) (decreases e)
let rec weakening g g' g'' e = match e with
  | EVar k     ->
     if k < (len g') then
       ()
     else
       (lookup_app_inv g (g' @ g'') (k + len g''); list_assoc g' g'' g)
  | EAbs t1 e1 -> weakening g (t1::g') g'' e1
  | EApp e1 e2 -> weakening g g' g'' e1; weakening g g' g'' e2

val free_in: exp -> nat -> Tot bool
let rec free_in e x = match e with
  | EVar k     -> k = x
  | EAbs _ e1  -> free_in e1 (x + 1)
  | EApp e1 e2 -> free_in e1 x || free_in e2 x

(* if g' @ (t::g) |- e : t and (len g') is not free in e, then we can essentially drop t from gamma (but adjust the indices in e *)
val strengthening: g:env -> g':env -> t:typ -> e:exp{Some? (typing (g' @ (t::g)) e) /\ not (free_in e (len g'))} ->
                   Lemma (requires True) (ensures (Some? (typing (g' @ g) (shift e (len g' + 1) (-1))) /\
                                                   Some?.v (typing (g' @ g) (shift e (len g' + 1) (-1))) = Some?.v (typing (g' @ (t::g)) e))) (decreases e)
let rec strengthening g g' t e = match e with
  | EVar k     ->
     if k < len g' then
       (lookup_app_inv (t::g) g' k;
	lookup_app_inv g g' k)
     else
       (list_assoc_a g g' t;
	lookup_app_inv g (g' @ [t]) k;
	lookup_ext_f g (k - (len g' + 1)) g')
  | EAbs t1 e1 -> strengthening g (t1::g') t e1
  | EApp e1 e2 -> strengthening g g' t e1; strengthening g g' t e2

(* some invariants for shift and free: a bit hacky *)
val shift_free: e:exp -> c:nat -> d:int{d >= -1 /\ (d = -1 ==> (not (free_zero e) \/ c > 0))} -> x:nat{x >= c} ->
                     Lemma (requires True)
			   (ensures (((d >= 0 ==> (free_in e x <==> free_in (shift e c d) (x + d)))) /\
				     (x < d + c ==> not (free_in (shift e c d) x))                   /\
                                     (not (free_in e c) ==> shift e c d = shift e (c + 1) d)))
let rec shift_free e c d x = match e with
  | EVar k     -> ()
  | EAbs _ e1  -> shift_free e1 (c + 1) d (x + 1)
  | EApp e1 e2 -> shift_free e1 c d x; shift_free e2 c d x

(* if e2 does not have j free, then e1[j |-> e2] does not have j free *)
val subst_elims_free: e1:exp -> j:nat -> e2:exp -> Lemma (requires (not (free_in e2 j)))
                                                         (ensures  (not (free_in (substitute e1 j e2) j)))
let rec subst_elims_free e1 j e2 = match e1 with
  | EVar k       -> ()
  | EAbs _ e1'   ->
     (shift_free e2 0 1 j;
      subst_elims_free e1' (j + 1) (shift e2 0 1))
  | EApp e1' e2' -> subst_elims_free e1' j e2; subst_elims_free e2' j e2

(* the substitution expression, the last n+1 perhaps can be n ? *)
val sexp: e1:exp -> n:nat -> e2:exp -> Tot exp
let sexp e1 n e2 = shift (substitute e1 n (shift e2 0 (n + 1))) (n + 1) (-1)

(*
 * if g |- e2 : t2, g' @ (t2::g) |- e1 : t1, then g' @ g |- sexp e1 (len g') e2 : t1
 *)
val subst_lem: g:env -> e2:exp{Some? (typing g e2)} -> g':env -> e1:exp{Some? (typing (g' @ ((Some?.v (typing g e2))::g)) e1)} ->
               Lemma (requires True) (ensures (Some? (typing (g' @ g) (sexp e1 (len g') e2)) /\
                                               Some?.v (typing (g' @ g) (sexp e1 (len g') e2)) = Some?.v (typing (g' @ ((Some?.v (typing g e2))::g)) e1)))
                                     (decreases e1)
let rec subst_lem g e2 g' e1 =
  let t = Some?.v (typing g e2) in
  match e1 with
  | EVar k        ->
     if k < len g' then
       (lookup_app_inv (t::g) g' k; lookup_app_inv g g' k)
     else if k > len g' then
       (list_assoc_a g g' t; lookup_app_inv g (g' @ [t]) k;
	lookup_ext_f g (k - (len g' + 1)) g')
     else
       (list_assoc_a g g' t;
	weakening g [] (g' @ [t]) e2;
	shift_free e2 0 (len g' + 1) (len g');
	strengthening g g' t (shift e2 0 (len g' + 1)))
  | EAbs t1' e1'  ->
     (list_assoc_b g g' t1' t;
      subst_lem g e2 (t1'::g') e1';
      consec_shifts_lem e2 0 (len g' + 1) 1)
  | EApp e1' e2'  -> subst_lem g e2 g' e1'; subst_lem g e2 g' e2'

val preservation: g:env -> e:exp{Some? (typing g e)} ->
                  Lemma (requires True)
                  (ensures (Some? (step e) ==>
                            (Some? (typing g (Some?.v (step e))) /\
                             Some?.v (typing g (Some?.v (step e))) = Some?.v (typing g e))))
                  (decreases e)
let rec preservation g e = match e with
  | EApp e1 e2 ->
     if is_value e1 then
       if is_value e2 then
       (match e1 with
	| EAbs _ e1' ->
	   (subst_lem g e2 [] e1';
	    shift_free e2 0 1 0;
	    subst_elims_free e1' 0 (shift e2 0 1);
	    shift_free (substitute e1' 0 (shift e2 0 1)) 0 (-1) ((* don't care argument *)1))
       )
       else
	 preservation g e2
     else
       preservation g e1
  | _ -> ()

(*
(* some tests for step, don't care about types *)
(*let id = EAbs TBool (EVar 0) (* \x.x *)
let id_app_id = EApp id id (* (\x.x) (\x.x) *)

let test0 = assert (Some? (step id_app_id) /\ Some?.v (step id_app_id) = id)

let self_app = EAbs TBool (EApp (EVar 0) (EVar 0)) (* \x. x x *)
let self_app_app_id = EApp self_app id

let test1 = assert (Some? (step self_app_app_id) /\ Some?.v (step self_app_app_id) = id_app_id)

let self_app_app_self_app = EApp self_app self_app
let test2 = assert (Some? (step self_app_app_self_app) /\ Some?.v (step self_app_app_self_app) = self_app_app_self_app)

(* two binders *)
let app_fn = EAbs TBool (EAbs TBool (EApp (EVar 1) (EVar 0))) (* \x \y. x y *)
let app_fn_app_id_id = EApp (EApp app_fn id) id

let s2 =
  let s1 = step app_fn_app_id_id in
  match s1 with
  | None -> None
  | Some s1' -> step s1'

let test3 = assert (Some? s2 /\ Some?.v s2 = id_app_id)*)
 *)
