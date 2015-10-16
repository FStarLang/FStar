(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdSetProps;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst listTot.fst ordset.fsi ordsetproperties.fst
  --*)
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

(* type lset 'a = l:list 'a{noRepeats l} *)

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
  
type subst = list (int * term)

val subst_term : subst -> term -> Tot term 
let rec subst_term s t = match t with 
  | V x -> 
    begin match assoc x s with 
      | None -> V x
      | Some y -> y
    end
  | F t1 t2 -> F (subst_term s t1) (subst_term s t2)

val subst_subst: subst -> subst -> Tot subst
let subst_subst s1 s2 = map (fun (x, t) -> (x, subst_term s1 t)) s2

val subst_eqns : subst -> eqns -> Tot eqns 
let subst_eqns s eqns = map (fun (t_1, t_2) -> subst_term s t_1, subst_term s t_2) eqns
 
val unify : e:eqns -> subst -> Tot (option subst)
  (decreases %[n_evars e; efuns e; n_flex_rhs e])
let rec unify e s = match e with 
  | [] -> Some s

  | (V x, t)::tl -> 
    if is_V t && V.i t = x
    then //t is a flex-rhs
         (assume (n_evars tl <= n_evars e);
          unify tl s)
    else if OrdSet.mem x (vars t) //occurs
    then None
    else (assume (n_evars (subst_eqns [x,t] tl) < n_evars e); //x is eliminated 
          unify (subst_eqns [x,t] tl) ((x,t)::s))

 | (t, V x)::tl -> //flex-rhs
   let e' = (V x, t)::tl in
   evars_permute_hd t (V x) tl;
   unify ((V x, t)::tl) s

 | (F t1 t2, F t1' t2')::tl -> //efuns reduces
   evars_unfun t1 t2 t1' t2' tl;
   unify ((t1, t1')::(t2, t2')::tl) s

