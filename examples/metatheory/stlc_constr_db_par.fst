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

module StlcConstrDeBruijnParallelSub

(* Constructive style progress and preservation proof for STLC with
   CBV reduction, using deBruijn indices and parallel substitution.
   An awkward special case pf stlc_strongred.fst; in fact this proof
   is _more_ complex than the one in stlc_strongred.fst! *)

open StlcStrongRed

val step : exp -> Tot (option exp)
let rec step e =
  match e with
  | EApp e1 e2 ->
      if is_value e1 then
        if is_value e2 then
          match e1 with
          | EAbs t e' -> Some (subst_beta e2 e')
          | _         -> None
        else
          match (step e2) with
          | Some e2' -> Some (EApp e1 e2')
          | None     -> None
      else
        (match (step e1) with
        | Some e1' -> Some (EApp e1' e2)
        | None     -> None)
  | _ -> None

val progress : #e:exp -> #t:ty -> h:rtyping empty e t ->
      Lemma (ensures (is_value e \/ (is_Some (step e)))) (decreases h)
let rec progress _ _ h =
  match h with
  | TyVar _   -> ()
  | TyAbs _ _ -> ()
  | TyApp h1 h2 -> progress h1; progress h2


val free_in_context : x:var -> #e:exp -> #g:env -> #t:ty -> h:rtyping g e t ->
      Lemma (ensures (appears_free_in x e ==> is_Some (g x))) (decreases h)
let rec free_in_context x _ _ _ h =
  match h with
  | TyVar x -> ()
  | TyAbs t h1 -> free_in_context (x+1) h1
  | TyApp h1 h2 -> free_in_context x h1; free_in_context x h2

val typable_empty_not_free : x:var -> #e:exp -> #t:ty -> rtyping empty e t ->
      Lemma (ensures (not (appears_free_in x e)))
(*      [SMTPat (appears_free_in x e)] -- CH: adding this makes it fail! *)
let typable_empty_not_free x _ _ h = free_in_context x h

val below : x:var -> e:exp -> Tot bool (decreases e)
let rec below x e =
  match e with
  | EVar y -> y < x
  | EApp e1 e2 -> below x e1 && below x e2
  | EAbs _ e1 -> below (x+1) e1

val closed : exp -> Tot bool
let closed = below 0

(* at some point we could try again to relate closed and appears_free *)
assume val forall_intro : #a:Type -> #p:(a -> Type) ->
  (x:a -> Lemma (p x)) -> Lemma (forall (x:a). p x)
(* this didn't work for some reason
  forall_intro #var #(fun (x:var) -> not (appears_free_in x e))
    (fun (x:var) -> typable_empty_closed x h)
*)
type pclosed (e:exp) = (forall (x:var). not (appears_free_in x e))
assume val closed_appears_free : e:exp{closed e} -> Lemma (ensures (pclosed e))
assume val appears_free_closed : e:exp{pclosed e} -> Lemma (ensures (closed e))
(*
let rec appears_free_closed e =
  match e with
  | EVar _ -> ()
  | EApp e1 e2 -> appears_free_closed e1; appears_free_closed e2
  | EAbs _ e1 -> appears_free_closed e1
*)

type below_env (x:var) (g:env) = (forall (y:var). y >= x ==> g y = None)

val typable_below : x:var -> #g:env{below_env x g} -> #e:exp -> #t:ty
                          -> h:rtyping g e t ->
      Lemma (ensures (below x e)) (decreases h)
let rec typable_below x g _ _ h =
  match h with
  | TyVar y -> ()
  | TyApp h1 h2 -> typable_below x h1; typable_below x h2
  | TyAbs _y h1 -> typable_below (x+1) h1

val typable_empty_closed : #e:exp -> #t:ty -> h:rtyping empty e t ->
      Lemma (ensures (closed e))
let typable_empty_closed e t h = typable_below 0 h



val subst_gen_var_lt : x:var -> y:var{y < x} -> v:exp -> Lemma
  (ensures (subst_beta_gen x v (EVar y) = (EVar y)))
let subst_gen_var_lt x y v = ()

val extend_lt : x:var -> y:var{y < x} -> g:env -> t_x:ty -> Lemma
     (ensures (extend g x t_x) y = g y)
let extend_lt x y g t_x = ()

val extend_gt : x:var -> y:var{y > x} -> g:env -> t_x:ty -> Lemma
     (ensures (extend g x t_x) y = g (y-1))
let extend_gt x y g t_x = ()

val extend_twice : x:var -> g:env -> t_x:ty -> t_y:ty -> Lemma
      (ensures (Equal (extend (extend g x t_x) 0     t_y)
                      (extend (extend g 0 t_y) (x+1) t_x)))
let extend_twice x g t_x t_y = ()

type sub_below (x:var) (s:sub) = (forall (y:var). y<x ==> s y = EVar y)

val subst_below : x:var -> v:exp{below x v} -> s:sub{sub_below x s} -> 
  Lemma (ensures (v = subst v s)) (decreases v)
let rec subst_below x v s =
  match v with
  | EVar y     -> ()
  | EApp e1 e2 -> subst_below x e1 s; subst_below x e2 s
  | EAbs t e   -> (subst_below (x+1) e (subst_eabs s);
                   assert(e = subst e (subst_eabs s));
                   assert(v = EAbs t e);
                   assert(subst v s = EAbs t (subst e (subst_eabs s)))) 

val subst_closed : v:exp{closed v} -> s:sub -> 
  Lemma (ensures (v = subst v s)) (decreases v)
let rec subst_closed v s = subst_below 0 v s

val subst_gen_eabs_aux : x:var -> v:exp{closed v} -> y:var -> Lemma
      (ensures ((subst_eabs (subst_beta_gen_aux  x    v)) y =
                            (subst_beta_gen_aux (x+1) v)  y))
let subst_gen_eabs_aux x v y =
  if y = 0 then ()
  else
    (assert((subst_eabs (subst_beta_gen_aux x v)) y =
           (subst (subst_beta_gen_aux x v (y-1)) inc_var));
          if y-1 < x then ()
     else if y-1 = x then
            (assert(subst_beta_gen_aux x v (y-1) = v);
             assert(subst_beta_gen_aux (x+1) v y = v);
             subst_closed v inc_var)
     else ())

val subst_gen_eabs_aux_forall : x:var -> v:exp{closed v} -> Lemma
      (ensures (SubEqual (subst_eabs (subst_beta_gen_aux  x    v))
                                     (subst_beta_gen_aux (x+1) v)))
let subst_gen_eabs_aux_forall x v = admit()
(* should follow from subst_gen_eabs_aux and forall_intro *)

val subst_gen_eabs : x:var -> v:exp{closed v} -> t_y:ty -> e':exp -> Lemma
      (ensures (subst_beta_gen x v (EAbs t_y e') =
                EAbs t_y (subst_beta_gen (x+1) v e')))
let subst_gen_eabs x v t_y e' =
  subst_gen_eabs_aux_forall x v;
  subst_extensional (subst_eabs (subst_beta_gen_aux  x    v))
                                      (subst_beta_gen_aux (x+1) v)  e';
  assert(subst_beta_gen x v (EAbs t_y e')
           = EAbs t_y (subst e' (subst_eabs (subst_beta_gen_aux x v))))

(* [some comment that might help here]
   NS: The trouble is that you need extensionality for this proof to go through. 
   [snip]
   A good way to solve this would be to use the same recipe
   that is being used in partialmap.fst for set, map etc. 

   -- Ideally, we would implement Map in the same style as Set, using
       functions (rather than axioms).

   -- Then, define Map.Equal to be extensional equality on maps, and
       admit one axiom, i.e, Extensional, allowing extensional maps to
       be treated as syntactically equal.
 
   -- Define type sub = Map.map var exp

   -- Then, prove a lemma:
        val subst_extensional: s1:sub -> s2:sub -> e:exp -> Lemma (ensures (Map.Equal s1 s2) ==> (subst e s1 = subst e s2))
                                                                  [SMTPat [subst e s1; subst e s2])

        let subst_extensional s1 s2 e = () //the proof should be trivial with the extensionality axiom

   -- With this, your proof should just go through trivially.
     
      Be aware that you will really need that SMTPat. 
      Let's look at the goal again:

         EApp (subst e1 s1) (subst e2 s1) = EApp (subst e1 s2) (subst e2 s3) 

      You really don't have a way to get your hands on s1, s2,
      s3. These are terms that come up as Z3 tries to search for a
      proof. Since you can't get your hands on it, you will not be
      able to call subst_extensional yourself. The SMT pat lets solver
      call it when it needs to.

      It would be nice if you could get your hands on s1, s2, s3
      somehow ... but I don't know of a way to do it at the moment.

      One improvement: maybe you don't want subst_extensional
      polluting the proof context at the top-level. You could instead
      write something like:

      val use_subst_extensional: unit -> Lemma (ensures (forall s1 s2 e.{:pattern subst e s1; subst e s2}
                                                               (Map.Equal s1 s2) ==> (subst e s1 = subst e s2)))

      And then call it just in the scope where you want the solver to make use of it.
      
 *)

val substitution_preserves_typing :
      x:var -> #e:exp -> #v:exp -> #t_x:ty -> #t:ty -> #g:env ->
      h1:rtyping empty v t_x ->
      h2:rtyping (extend g x t_x) e t ->
      Tot (rtyping g (subst_beta_gen x v e) t) (decreases e)
let rec substitution_preserves_typing x e v t_x t g h1 h2 =
  match h2 with
  | TyVar y ->
     if x=y then      (typable_empty_closed h1;
                       closed_appears_free v;
                       context_invariance h1 g)
     else if y<x then context_invariance h2 g
     else             TyVar (y-1)
  | TyAbs #g' t_y #e' #t' h21 ->
     (let h21' = typing_extensional h21 (extend (extend g 0 t_y) (x+1) t_x) in
      typable_empty_closed h1;
      subst_gen_eabs x v t_y e';
      TyAbs t_y (substitution_preserves_typing (x+1) h1 h21'))
  | TyApp #g' #e1 #e2 #t11 #t12 h21 h22 ->
     (* CH: implicits don't work here, why? *)
    (TyApp #g #(subst_beta_gen x v e1) #(subst_beta_gen x v e2) #t11 #t12
       (substitution_preserves_typing x h1 h21)
       (substitution_preserves_typing x h1 h22))

val preservation : #e:exp{is_Some (step e)} -> #t:ty -> h:(rtyping empty e t) ->
      Tot (rtyping empty (Some.v (step e)) t) (decreases e)
let rec preservation e t h =
  let TyApp #g #e1 #e2 #t11 #t12 h1 h2 = h in
     if is_value e1
     then (if is_value e2
           then let TyAbs t_x hbody = h1 in
                substitution_preserves_typing 0 h2 hbody
           else TyApp h1 (preservation h2))
     else TyApp (preservation h1) h2
