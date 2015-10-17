(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdSetProps;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst listTot.fst ordset.fsi ordsetproperties.fst
  --*)
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
   An implementation of first-order unification, based on 
     Ana Bove's Licentiate Thesis
     Programming in Martin-Löf Type Theory Unification - A non-trivial Example
     Department of Computer Science, Chalmers University of Technology
     1999
     http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.40.3532
*)   

(* STILL INCOMPLETE *)
module Unification

open FStar.List.Tot

val union : list 'a -> list 'a -> Tot (list 'a)
let rec union l m = match l with
  | [] -> m
  | hd::tl ->
    if mem hd m
    then union tl m
    else union tl (hd::m)

val no_dups_union: l:list 'a -> m:list 'a ->
  Lemma (requires (noRepeats m))
        (ensures (noRepeats (union l m)))
let rec no_dups_union l m = match l with
  | [] -> ()
  | hd::tl ->
    if mem hd m
    then no_dups_union tl m
    else no_dups_union tl (hd::m)

type term = 
  | V : i:nat -> term
  | F : t1:term -> t2:term -> term

val nat_order : OrdSet.cmp nat
let nat_order x y = x <= y

type varset = OrdSet.ordset nat nat_order
val empty_vars : varset
let empty_vars = OrdSet.empty

type eqns  = list (term * term) 

val vars : term -> Tot varset
let rec vars = function 
  | V i -> OrdSet.singleton i
  | F t1 t2 -> OrdSet.union (vars t1) (vars t2) 

val evars : eqns -> Tot varset
let rec evars = function
  | [] -> empty_vars
  | (x, y)::tl -> OrdSet.union (OrdSet.union (vars x) (vars y)) (evars tl)
  
val n_evars : eqns -> Tot nat
let n_evars eqns = OrdSet.size (evars eqns)

val evars_permute_hd : x:term -> y:term -> tl:eqns -> Lemma 
  (ensures (evars ((x, y)::tl) = evars ((y, x)::tl)))
let evars_permute_hd x y tl = OrdSet.eq_lemma (evars ((x,y)::tl)) (evars ((y,x)::tl))

val evars_unfun : x:term -> y:term -> x':term -> y':term -> tl:eqns -> Lemma
  (ensures (evars ((F x y, F x' y')::tl) = evars ((x, x')::(y, y')::tl)))
let evars_unfun x y x' y' tl = OrdSet.eq_lemma (evars ((F x y, F x' y')::tl)) (evars ((x, x')::(y, y')::tl))

val funs : term -> Tot nat
let rec funs = function 
  | V _ -> 0
  | F t1 t2 -> 1 + funs t1 + funs t2

val efuns : eqns -> Tot nat
let rec efuns = function 
  | [] -> 0
  | (x,y)::tl -> funs x + funs y + efuns tl

val efuns_smaller: t1:term -> t2:term -> tl:eqns -> Lemma
  (ensures (efuns tl <= efuns ((t1, t2)::tl)))
let efuns_smaller t1 t2 tl = ()

val efuns_permute_hd : x:term -> y:term -> tl:eqns -> Lemma
  (ensures (efuns ((x,y)::tl) = efuns ((y,x)::tl)))
let efuns_permute_hd x y tl = ()  

val n_flex_rhs : eqns -> Tot nat
let rec n_flex_rhs = function
  | [] -> 0
  | (V _, V _)::tl
  | (_  , V _)::tl -> 1 + n_flex_rhs tl
  | _::tl -> n_flex_rhs tl
  
type subst = (nat * term)

val subst_term : subst -> term -> Tot term 
let rec subst_term s t = match t with 
  | V x -> if x = fst s then snd s else V x
  | F t1 t2 -> F (subst_term s t1) (subst_term s t2)

type subst_ok s = ~ (OrdSet.mem (fst s) (vars (snd s)))

val lemma_vars_decrease: s:subst -> t':term -> Lemma 
  (requires (subst_ok s))
  (ensures (OrdSet.subset (vars (subst_term s t'))
 			  (OrdSet.remove (fst s) (OrdSet.union (vars (snd s)) (vars t')))))
let rec lemma_vars_decrease s t' = match t' with 
  | V x -> ()
  | F t1 t2 -> 
    lemma_vars_decrease s t1;
    lemma_vars_decrease s t2

val subst_subst: subst -> list subst -> Tot (list subst)
let subst_subst s1 s2 = map (fun (x, t) -> (x, subst_term s1 t)) s2

val subst_eqns : subst -> eqns -> Tot eqns 
let rec subst_eqns s eqns = match eqns with 
  | [] -> []
  | (t_1, t_2)::tl -> (subst_term s t_1, subst_term s t_2) :: subst_eqns s tl

type strict_subset (v1:varset) (v2:varset) = OrdSet.subset v1 v2 /\ ~(OrdSet.Equal v1 v2)

val vars_decrease_eqns: x:nat -> t:term -> e:eqns -> Lemma
  (requires (subst_ok (x, t)))
  (ensures (OrdSet.subset (evars (subst_eqns (x,t) e))
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
    if is_V t && V.i t = x
    then unify tl s //t is a flex-rhs
    else if OrdSet.mem x (vars t) //occurs
    then None
    else (vars_decrease_eqns x t tl;
          unify (subst_eqns (x,t) tl) ((x,t)::subst_subst (x,t) s))

 | (t, V x)::tl -> //flex-rhs
   evars_permute_hd t (V x) tl;
   unify ((V x, t)::tl) s

 | (F t1 t2, F t1' t2')::tl -> //efuns reduces
   evars_unfun t1 t2 t1' t2' tl;
   unify ((t1, t1')::(t2, t2')::tl) s

