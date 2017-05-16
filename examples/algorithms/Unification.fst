(*
   Copyright 2008-2015 Nikhil Swamy and Microsoft Research

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

(* 
   A verified implementation of first-order unification. 

   The termination argument is based on  Ana Bove's Licentiate Thesis:
         Programming in Martin-Löf Type Theory Unification - A non-trivial Example
	 Department of Computer Science, Chalmers University of Technology
	 1999
	 http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.40.3532

   But, is done here directly with lex orderings.
*)   

module Unification

open FStar.List.Tot

(* First, a missing lemma from the list library *)
let op_At = append
val lemma_shift_append: #a:eqtype -> l:list a -> x:a -> m:list a -> Lemma
  (ensures ( (l@(x::m)) = ((l@[x])@m)))
let rec lemma_shift_append #a l x m = match l with
  | [] -> ()
  | hd::tl -> lemma_shift_append tl x m

(* A term language with variables V and pairs F *)
type term =
  | V : i:nat -> term
  | F : t1:term -> t2:term -> term

(* Finite, ordered sets of variables *)
val nat_order : OrdSet.cmp nat
let nat_order x y = x <= y
type varset = OrdSet.ordset nat nat_order

val empty_vars : varset
let empty_vars = OrdSet.empty

(* Collecting the variables in a term *)
val vars : term -> Tot varset
let rec vars = function
  | V i -> OrdSet.singleton i
  | F t1 t2 -> OrdSet.union (vars t1) (vars t2)

(* Equations among pairs of terms, to be solved *)
type eqns  = list (term * term)

(* All the variables in a set of equations *)
val evars : eqns -> Tot varset
let rec evars = function
  | [] -> empty_vars
  | (x, y)::tl -> OrdSet.union (OrdSet.union (vars x) (vars y)) (evars tl)

(* Counting variables; used in the termination metric *)
val n_evars : eqns -> Tot nat
let n_evars eqns = OrdSet.size (evars eqns)

(* Counting the number of F-applications; also for the termination metric *)
val funs : term -> Tot nat
let rec funs = function
  | V _ -> 0
  | F t1 t2 -> 1 + funs t1 + funs t2

val efuns : eqns -> Tot nat
let rec efuns = function
  | [] -> 0
  | (x,y)::tl -> funs x + funs y + efuns tl

(* Counting the number of equations with variables on the the RHS;
   also for the termination metric *)
val n_flex_rhs : eqns -> Tot nat
let rec n_flex_rhs = function
  | [] -> 0
  | (V _, V _)::tl
  | (_  , V _)::tl -> 1 + n_flex_rhs tl
  | _::tl -> n_flex_rhs tl

(* A point substitution *)
type subst = (nat * term)

(* Composition of point substitions *)
type lsubst = list subst

val subst_term : subst -> term -> Tot term
let rec subst_term s t = match t with
  | V x -> if x = fst s then snd s else V x
  | F t1 t2 -> F (subst_term s t1) (subst_term s t2)

val lsubst_term : list subst -> term -> Tot term
let lsubst_term = fold_right subst_term

let occurs x t = OrdSet.mem x (vars t)
let ok s = not (occurs (fst s) (snd s))

val lsubst_eqns: list subst -> eqns -> Tot eqns
let rec lsubst_eqns l = function
  | [] -> []
  | (x,y)::tl -> (lsubst_term l x, lsubst_term l y)::lsubst_eqns l tl

val lemma_lsubst_eqns_nil: e:eqns -> Lemma
  (requires True)
  (ensures (lsubst_eqns [] e = e))
  [SMTPat (lsubst_eqns [] e)]
let rec lemma_lsubst_eqns_nil = function
  | [] -> ()
  | _::tl -> lemma_lsubst_eqns_nil tl

(* A couple of lemmas about variable counts.
   Both of these rely on extensional equality of sets.
   So we need to use eq_lemma explicitly *)
val evars_permute_hd : x:term -> y:term -> tl:eqns -> Lemma
  (ensures (evars ((x, y)::tl) = evars ((y, x)::tl)))
let evars_permute_hd x y tl = OrdSet.eq_lemma (evars ((x,y)::tl)) (evars ((y,x)::tl))

val evars_unfun : x:term -> y:term -> x':term -> y':term -> tl:eqns -> Lemma
  (ensures (evars ((F x y, F x' y')::tl) = evars ((x, x')::(y, y')::tl)))
let evars_unfun x y x' y' tl = OrdSet.eq_lemma (evars ((F x y, F x' y')::tl)) (evars ((x, x')::(y, y')::tl))

(* Eliminating a variable reduces the variable count *)
val lemma_vars_decrease: s:subst -> t':term -> Lemma
  (requires (ok s))
  (ensures (OrdSet.subset (vars (subst_term s t'))
 			  (OrdSet.remove (fst s) (OrdSet.union (vars (snd s)) (vars t')))))
let rec lemma_vars_decrease s t' = match t' with
  | V x -> ()
  | F t1 t2 ->
    lemma_vars_decrease s t1;
    lemma_vars_decrease s t2

(* Lifting the prior lemma to equations *)
val vars_decrease_eqns: x:nat -> t:term -> e:eqns -> Lemma
  (requires (ok (x, t)))
  (ensures (OrdSet.subset (evars (lsubst_eqns [x,t] e))
			  (OrdSet.remove x (evars ((V x, t)::e)))))
let rec vars_decrease_eqns x t e = match e with
  | [] -> ()
  | hd::tl -> lemma_vars_decrease (x,t) (fst hd);
	    lemma_vars_decrease (x,t) (snd hd);
	    vars_decrease_eqns x t tl
 
val unify : e:eqns -> list subst -> Tot (option (list subst))
  (decreases %[n_evars e; efuns e; n_flex_rhs e])
let rec unify e s = match e with
  | [] -> Some s

  | (V x, t)::tl ->
    if V? t && V?.i t = x
    then unify tl s //t is a flex-rhs
    else if occurs x t
    then None
    else (vars_decrease_eqns x t tl;
          unify (lsubst_eqns [x,t] tl) ((x,t)::s))

 | (t, V x)::tl -> //flex-rhs
   evars_permute_hd t (V x) tl;
   unify ((V x, t)::tl) s

 | (F t1 t2, F t1' t2')::tl -> //efuns reduces
   evars_unfun t1 t2 t1' t2' tl;
   unify ((t1, t1')::(t2, t2')::tl) s

(* All equations are solved when each one is just reflexive *)
val solved : eqns -> Tot bool
let rec solved = function
  | [] -> true
  | (x,y)::tl -> x=y && solved tl

val lsubst_distributes_over_F: l:list subst -> t1:term -> t2:term -> Lemma
       (requires (True))
       (ensures (lsubst_term l (F t1 t2) = F (lsubst_term l t1) (lsubst_term l t2)))
       [SMTPat (lsubst_term l (F t1 t2))]
let rec lsubst_distributes_over_F l t1 t2 = match l with
  | [] -> ()
  | hd::tl -> lsubst_distributes_over_F tl t1 t2

let extend_subst s l = s::l
let extend_lsubst l l' = l @ l'
 
val lemma_extend_lsubst_distributes_term: l:list subst -> l':list subst -> e:term -> Lemma
       (requires True)
       (ensures (lsubst_term (extend_lsubst l l') e = lsubst_term l (lsubst_term l' e)))
let rec lemma_extend_lsubst_distributes_term l l' e = match l with
  | [] -> ()
  | hd::tl -> lemma_extend_lsubst_distributes_term tl l' e

val lemma_extend_lsubst_distributes_eqns: l:list subst -> l':list subst -> e:eqns -> Lemma
       (requires True)
       (ensures (lsubst_eqns (extend_lsubst l l') e = lsubst_eqns l (lsubst_eqns l' e)))
       [SMTPat (lsubst_eqns (extend_lsubst l l') e)]
let rec lemma_extend_lsubst_distributes_eqns l l' e = match e with
  | [] -> ()
  | (t1, t2)::tl ->
    lemma_extend_lsubst_distributes_term l l' t1;
    lemma_extend_lsubst_distributes_term l l' t2;
    lemma_extend_lsubst_distributes_eqns l l' tl

val lemma_subst_id: x:nat -> z:term -> y:term -> Lemma
  (requires (not (occurs x y)))
  (ensures (subst_term (x,z) y = y))
let rec lemma_subst_id x z y = match y with
  | V x' -> ()
  | F t1 t2 -> lemma_subst_id x z t1; lemma_subst_id x z t2

let neutral s (x, t)   = subst_term s (V x) = V x  && subst_term s t = t  && ok (x, t)
let neutral_l l (x, t) = lsubst_term l (V x) = V x && lsubst_term l t = t && ok (x, t)

val lemma_lsubst_term_commutes: s:subst -> l:list subst -> e:term -> Lemma
  (requires (neutral_l l s))
  (ensures (lsubst_term [s] (lsubst_term l (subst_term s e)) =
	    lsubst_term [s] (lsubst_term l e)))
let rec lemma_lsubst_term_commutes s l e = match e with
  | V y -> lemma_subst_id (fst s) (snd s) (snd s)
    
  | F t1 t2 -> lemma_lsubst_term_commutes s l t1;
	      lemma_lsubst_term_commutes s l t2
  
val lemma_lsubst_eqns_commutes: s:subst -> l:list subst -> e:eqns -> Lemma
  (requires (neutral_l l s))
  (ensures (lsubst_eqns [s] (lsubst_eqns l (lsubst_eqns [s] e)) =
	    lsubst_eqns [s] (lsubst_eqns l e)))
let rec lemma_lsubst_eqns_commutes s l = function
  | [] -> ()
  | (t1,t2)::tl -> lemma_lsubst_term_commutes s l t1;
		 lemma_lsubst_term_commutes s l t2;
		 lemma_lsubst_eqns_commutes s l tl

let (++) l1 l2 = extend_lsubst l1 l2
let sub l e = lsubst_eqns l e

let test l1 l2 l3 = assert (l1 ++ l2 ++ l3 == (l1 ++ l2) ++ l3)

val key_lemma: x:nat -> y:term -> tl:eqns -> l:list subst -> lpre:list subst -> l'':list subst -> Lemma
  (requires (l'' = lpre ++ ([x,y] ++ l)
	     /\ not (occurs x y)
 	     /\ l `sub` ((V x, y)::tl) = (V x, y)::tl
 	     /\ solved (l'' `sub` ([x, y] `sub` tl))))
  (ensures (solved (l'' `sub` ((V x,y)::tl))))

let key_lemma x y tl l lpre l'' =
  let xy = [x,y] in
  let xyl = xy++l in
  let vxy = V x, y in
  assert  (l'' `sub` (vxy::tl)
        == lpre `sub` (xy `sub` (l `sub` (vxy::tl))));
  lemma_lsubst_eqns_commutes (x,y) l (vxy :: tl);
  assert  (lpre `sub` (xy `sub` (l `sub` (vxy::tl)))
        == lpre `sub` (xy `sub` (l `sub` (xy `sub` (vxy::tl)))));
  assert  (lpre `sub` (xy `sub` (l `sub` (xy `sub` (vxy::tl))))
        == l'' `sub` (xy `sub` (vxy :: tl)));
  lemma_subst_id x y y

val lemma_subst_term_idem: s:subst -> t:term -> Lemma
  (requires (ok s))
  (ensures (subst_term s (subst_term s t) = subst_term s t))
let rec lemma_subst_term_idem s t = match t with
  | V x -> lemma_subst_id (fst s) (snd s) (snd s)
  | F t1 t2 -> lemma_subst_term_idem s t1; lemma_subst_term_idem s t2

val lemma_subst_eqns_idem: s:subst -> e:eqns -> Lemma
  (requires (ok s))
  (ensures (lsubst_eqns [s] (lsubst_eqns [s] e) = lsubst_eqns [s] e))
let rec lemma_subst_eqns_idem s = function
  | [] -> ()
  | (x, y)::tl -> lemma_subst_eqns_idem s tl;
	        lemma_subst_term_idem s x;
	        lemma_subst_term_idem s y

val subst_funs_monotone: s:subst -> t:term -> Lemma
  (ensures (funs (subst_term s t) >= funs t))
let rec subst_funs_monotone s = function
  | V x -> ()
  | F t1 t2 -> subst_funs_monotone s t1; subst_funs_monotone s t2
  
val lsubst_funs_monotone: l:list subst -> t:term -> Lemma
  (ensures (funs (lsubst_term l t) >= funs t))
let rec lsubst_funs_monotone l t = match l with
  | [] -> ()
  | hd::tl ->
    lsubst_funs_monotone tl t; subst_funs_monotone hd (lsubst_term tl t)
    
val lemma_occurs_not_solveable_aux: x:nat -> t:term{occurs x t /\ not (V? t)} -> s:list subst -> Lemma
  (funs (lsubst_term s t) >= (funs t + funs (lsubst_term s (V x))))
let rec lemma_occurs_not_solveable_aux x t s = match t with
  | F t1 t2 ->
    if occurs x t1
    then let _ = lsubst_funs_monotone s t2 in
	 match t1 with
	   | V y -> ()
 	   | _ -> lemma_occurs_not_solveable_aux x t1 s
    else if occurs x t2
    then let _ = lsubst_funs_monotone s t1 in
	 match t2 with
	   | V y -> ()
 	   | _ -> lemma_occurs_not_solveable_aux x t2 s
    else ()

type not_solveable s =
  forall l. lsubst_term l (fst s) <> lsubst_term l (snd s)

val lemma_occurs_not_solveable: x:nat -> t:term -> Lemma
  (requires (occurs x t /\ not (V? t)))
  (ensures (not_solveable (V x, t)))
let lemma_occurs_not_solveable x t = FStar.Classical.forall_intro (lemma_occurs_not_solveable_aux x t)
 
val lemma_subst_idem: l:list subst -> x:nat -> t:term -> t':term -> Lemma
  (requires (lsubst_term l (V x) = lsubst_term l t))
  (ensures (lsubst_term l (subst_term (x,t) t') = lsubst_term l t'))
let rec lemma_subst_idem l x t t' = match t' with
  | V y -> ()
  | F t1 t2 -> lemma_subst_idem l x t t1; lemma_subst_idem l x t t2

val lemma_subst_eqns: l:list subst -> x:nat -> t:term -> e:eqns -> Lemma
  (requires (lsubst_term l (V x) = lsubst_term l t))
  (ensures (lsubst_eqns l (lsubst_eqns [x,t] e) = lsubst_eqns l e))
let rec lemma_subst_eqns l x t = function
  | [] -> ()
  | (t1,t2)::tl ->
    lemma_subst_idem l x t t1;
    lemma_subst_idem l x t t2;
    lemma_subst_eqns l x t tl

type not_solveable_eqns e =
  forall l. not (solved (lsubst_eqns l e))

val lemma_not_solveable_cons_aux: x:nat -> t:term -> tl:eqns -> l:list subst -> Lemma
  (requires (not_solveable_eqns (lsubst_eqns [x,t] tl)
	     /\ solved (lsubst_eqns l ((V x,t)::tl))))
  (ensures False)
  [SMTPat (solved (lsubst_eqns l ((V x,t)::tl)))]
let lemma_not_solveable_cons_aux x t tl l = lemma_subst_eqns l x t tl

val lemma_not_solveable_cons:  x:nat -> t:term -> tl:eqns -> Lemma
    (requires (not_solveable_eqns (lsubst_eqns [x,t] tl)))
    (ensures (not_solveable_eqns ((V x, t)::tl)))
let lemma_not_solveable_cons x t tl = ()

val unify_correct_aux: l:list subst -> e:eqns -> Pure (list subst)
 (requires (b2t (lsubst_eqns l e = e)))
 (ensures (fun m ->
	    match unify e l with
	      | None -> not_solveable_eqns e
	      | Some l' ->
		  l' = (m @ l)
		 /\ solved (lsubst_eqns l' e)))
 (decreases %[n_evars e; efuns e; n_flex_rhs e])
#set-options "--z3rlimit 20"
let rec unify_correct_aux l = function
  | [] -> []
  | hd::tl ->
    begin match hd with
      | (V x, y) ->
	if V? y && V?.i y=x
	then unify_correct_aux l tl
	else if occurs x y
	then (lemma_occurs_not_solveable x y; [])
	else begin
	     let s = (x,y) in
	     let l' = extend_subst s l in
	     vars_decrease_eqns x y tl;
	     let tl' = lsubst_eqns [s] tl in
	     lemma_extend_lsubst_distributes_eqns [s] l tl;
	     assert (lsubst_eqns l' tl' = lsubst_eqns [s] (lsubst_eqns l (lsubst_eqns [s] tl)));
	     lemma_lsubst_eqns_commutes s l tl;
	     lemma_subst_eqns_idem s tl;
	     let lpre = unify_correct_aux l' tl' in
	     begin match unify tl' l' with
	       | None -> lemma_not_solveable_cons x y tl; []
	       | Some l'' ->
		 key_lemma x y tl l lpre l'';
		 lemma_shift_append lpre s l;
		 lpre@[s]
	     end
	 end

      | (y, V x) ->
	evars_permute_hd y (V x) tl;
	unify_correct_aux l ((V x, y)::tl)

      | F t1 t2, F s1 s2 ->
	evars_unfun t1 t2 s1 s2 tl;
 	unify_correct_aux l ((t1, s1)::(t2, s2)::tl)
     end

val unify_eqns : e:eqns -> Tot (option lsubst)
let unify_eqns e = unify e []

val unify_eqns_correct: e:eqns -> Lemma
  (requires True)
  (ensures (if None? (unify_eqns e)
	    then not_solveable_eqns e
	    else solved (lsubst_eqns (Some?.v (unify_eqns e)) e)))
let unify_eqns_correct e =
  let _ = unify_correct_aux [] e in ()

  

// l = hd::tl
// s = x, t
// ------------------------------------------------------
// subst_term s (lsubst_term (subst_lsubst s l) t)
// = {def}
// subst_term s (subst_term (subst_subst s hd) (lsubst_term (subst_lsubst s tl) t))
// = {lemma_cancel_subst_subst s hd ...}
// subst_term s (subst_term hd                 (lsubst_term (subst_lsubst s tl) t))
// = {subst_term_commutes} (ok s; subst_term hd (V x) = (V x); subst_term hd t = t)
// subst_term s (subst_term hd (subst_term s  (lsubst_term (subst_lsubst s tl) t)))
// = {IH}
// subst_term s (subst_term hd (subst_term s (lsubst_term tl t)))
// = {subst_term_commutes}  (ok s; subst_term hd (V x) = (V x); subst_term hd t = t)
// subst_term s (subst_term hd (lsubst_term tl t))
// = {def}
// subst_term s (lsubst_term l tl)


// val subst_subst : subst -> subst -> Tot subst
// let subst_subst s1 (x, t) = (x, subst_term s1 t)

// val subst_lsubst: subst -> list subst -> Tot (list subst)
// let subst_lsubst s1 s2 = map (subst_subst s1) s2

// let lsubst_lsubst = fold_right subst_lsubst

// val lemma_cancel_subst_subst: s1:subst -> s2:subst -> t:term -> Lemma
//   (requires (ok s1))
//   (ensures (subst_term s1 (subst_term (subst_subst s1 s2) t) =
//             subst_term s1 (subst_term s2 t)))
// let rec lemma_cancel_subst_subst s1 s2 t = match t with 
//   | V x -> 
//     if x = fst s2
//     then begin assert (subst_term (subst_subst s1 s2) t = 
// 		       subst_term s1 (subst_term s2 t));
// 	       lemma_subst_term_idem s1 (subst_term s2 t)
//          end
//     else begin assert (subst_term s2 t = t); 
// 	       assert (subst_term (subst_subst s1 s2) t = t)
// 	 end

//   | F t1 t2 -> lemma_cancel_subst_subst s1 s2 t1;
// 	      lemma_cancel_subst_subst s1 s2 t2

// val lemma_cancel_subst_lsubst: s:subst -> l:list subst -> t:term -> Lemma
//     (requires (neutral_l l s))
//     (ensures (subst_term s (lsubst_term (subst_lsubst s l) t) = 
// 	      subst_term s (lsubst_term l t)))
// let rec lemma_cancel_subst_lsubst s l t = match l with 
//   | [] -> ()
//   | hd::tl -> 
//     assert (subst_lsubst s l = subst_subst s hd::subst_lsubst s tl); 
//     assert (lsubst_term (subst_lsubst s l) t = 
// 	    subst_term (subst_subst s hd) (lsubst_term (subst_lsubst s tl) t));
//     lemma_cancel_subst_subst s hd (lsubst_term (subst_lsubst s tl) t);

//     assert (subst_term s (lsubst_term (subst_lsubst s l) t) = 
// 	    subst_term s (subst_term hd (lsubst_term (subst_lsubst s tl) t)));

//     lemma_cancel_subst_lsubst s tl t; 
//     assert (subst_term s (lsubst_term (subst_lsubst s l) t) = 
// 	    subst_term s (subst_term hd (subst_term s (lsubst_term tl t))));
//     admit()


//     assert (subst_term s (lsubst_term (subst_lsubst s tl) t) = 
// 	    subst_term s (lsubst_term tl t))
// 	    ;
//     admit()
