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
module OPLSS2021.STLC

(** A deep embedding of the simply typed lambda calculus with
    call-by-value reduction, proving progress and preservation

    This is intentionally very simple. For example:
      
      - Variables are just concrete names
      
      - Can only substitute closed terms (no need for capture
        avoidance)
      
      - The type system is defined as a total function, rather than a
        relation
      
    All of this is okay in this simple, hello-world setting. But, a
    more serious development would make different choices

**)

/// We have just one base type: unit
/// And arrow types
type ty =
  | TUnit  : ty
  | TArrow : ty -> ty -> ty

/// We'll represent variables by integers, i.e., just concrete names
///
/// This is just a toy---it means that simple things like alpha
/// equivalence are not encoded in the syntax.
///
/// But, it keeps things easy for this small example.
///
/// E.g., (\(x:unit).x) can be represented as (EAbs 0 TUnit (EVar 0))
type exp =
  | EVar   : int -> exp             // x
  | EApp   : exp -> exp -> exp     // e1 e2
  | EAbs   : int -> ty -> exp -> exp  // \ x:t. e
  | EUnit  : exp                 // ()

/// Lambda terms and unit values are the results of computations
let is_value (e:exp) : bool =
  match e with
  | EAbs _ _ _
  | EUnit -> true
  | _ -> false

///  subst x e e': Substitute x for e in e'
/// 
///  This is a very simple definition of substitution
/// 
///  In particular, it doesn't bother with capture avoidance.  That's
///  because, in this particular example, `e` will always be a closed
///  term.
let rec subst (x:int) (e e':exp) : exp =
  match e' with
  | EVar x' -> 
    // If we've found the variable we're substituting for
    // replace it with e
    if x = x' then e else e'
  | EAbs x' t e1 ->
    EAbs x' t 
      (if x = x' 
       then e1 // If x' shadows x, then don't bother descending into e1
       else subst x e e1)
  | EApp e1 e2 -> 
    EApp (subst x e e1) (subst x e e2)
  | EUnit -> EUnit

/// A single step of reduction
///   The program may be stuck (e.g., because it's ill-typed)
///   Return None if so
let rec step (e:exp) : option exp =
  match e with
  | EApp e1 e2 ->
      if is_value e1 then
        if is_value e2 then
          match e1 with
          | EAbs x t e' -> Some (subst x e2 e')
          | _           -> None
        else
          match step e2 with
          | Some e2' -> Some (EApp e1 e2')
          | None     -> None
      else
        (match step e1 with
        | Some e1' -> Some (EApp e1' e2)
        | None     -> None)
  | _ -> None

////////////////////////////////////////////////////////////////////////////////
// Type checking 
////////////////////////////////////////////////////////////////////////////////

/// The type of an environment (often written Gamma)
///   A partial map from variables to their types
let env = int -> option ty

/// The empty environment
let empty : env = fun _ -> None

/// Extending an environment
///    g, x:t
let extend (g:env) (x:int) (t:ty) 
  : env 
  = fun x' -> if x = x' then Some t else g x'

/// typing g e:
///    A function to compute the type of `e` in the environment `g`
///    returns None if it is ill typed
let rec typing (g:env) (e:exp)
  : option ty
  = match e with
    | EVar x -> g x
    | EAbs x t e1 ->
      (match typing (extend g x t) e1 with
       | Some t' -> Some (TArrow t t')
       | None    -> None)
    | EApp e1 e2 ->
      (match typing g e1, typing g e2 with
       | Some (TArrow t11 t12), Some t2 -> if t11 = t2 then Some t12 else None
       | _                    , _       -> None)
  | EUnit -> Some TUnit

////////////////////////////////////////////////////////////////////////////////
// Syntactic metatheory: Progress and preservation lemmas
////////////////////////////////////////////////////////////////////////////////

/// Our first lemma about STLC is progress
///    A well-typed closed term is either
///    + a value
///    + can take a step
/// Its proof is pretty easy, just an induction on `e`
let rec progress (e:exp)
  : Lemma
      (requires Some? (typing empty e))
      (ensures is_value e \/ Some? (step e))
  = match e with
    | EAbs _ _ _ 
    | EUnit -> ()
    | EApp e1 e2 -> progress e1; progress e2

/// The proof of preservation will take a few more steps


/// First, we define when a variable `x` appears free in `e`
let rec appears_free_in (x:int) (e:exp)
  : bool 
  = match e with
    | EVar y -> x = y
    | EApp e1 e2 -> appears_free_in x e1 || appears_free_in x e2
    | EAbs y _ e1 -> x <> y && appears_free_in x e1
    | EUnit -> false

/// All the free variables of a term `e` well-typed in `g`
/// must be bound in `g`
let rec free_in_context (e:exp) (g:env)
  : Lemma
      (requires Some? (typing g e))
      (ensures forall x. appears_free_in x e ==> Some? (g x))
  = match e with
    | EVar _
    | EUnit -> ()
    | EAbs y t e1 -> free_in_context e1 (extend g y t)
    | EApp e1 e2 -> free_in_context e1 g; free_in_context e2 g

/// If we term is well-typed in the empty environment
/// then it has no free variables
let typable_empty_closed (e:exp)
  : Lemma  (requires Some? (typing empty e))
           (ensures forall x. not (appears_free_in x e))
  = free_in_context e empty

/// Pointwise equality of environments
let equal (g1:env) (g2:env) = forall (x:int). g1 x=g2 x

/// Equality of environments on the free variables of `e`
let equalE (e:exp) (g1:env) (g2:env) =
    forall (x:int). appears_free_in x e ==> g1 x=g2 x

/// If two environments agree on the free variables of `e`
/// then typing `e` in those two environments is equivalent
let rec context_invariance (e:exp) (g g':env)
  :  Lemma
     (requires equalE e g g')
     (ensures typing g e == typing g' e)
  = match e with
    | EAbs x t e1 ->
      context_invariance e1 (extend g x t) (extend g' x t)

    | EApp e1 e2 ->
      context_invariance e1 g g';
      context_invariance e2 g g'
    
    | _ -> ()

/// A stronger version of context invariance
let typing_extensional (g g':env) (e:exp)
  : Lemma
    (requires equal g g')
    (ensures typing g e == typing g' e)
  = context_invariance e g g'

/// The key substitution lemma:
///    Subsituting a closed term `v : t` for `x : t` in `e : t'`
///    produces a term of the same type
let rec substitution_preserves_typing (x:int) (e v:exp) (g:env)
  : Lemma
    (requires Some? (typing empty v) /\
              Some? (typing (extend g x (Some?.v (typing empty v))) e))
    (ensures typing g (subst x v e) ==
             typing (extend g x (Some?.v (typing empty v))) e)
  = let Some t_x = typing empty v in
    let gx = extend g x t_x in
    match e with
    | EUnit -> ()
    | EVar y ->
      if x=y
      then (
        typable_empty_closed v;
        context_invariance v empty g
      )
      else context_invariance e gx g
  
    | EApp e1 e2 ->
      substitution_preserves_typing x e1 v g;
      substitution_preserves_typing x e2 v g

    | EAbs y t_y e1 ->
      let gxy = extend gx y t_y in
      let gy = extend g y t_y in
      if x=y
      then typing_extensional gxy gy e1
      else
        (let gyx = extend gy x t_x in
         typing_extensional gxy gyx e1;
         substitution_preserves_typing x e1 v gy)

/// Preservation:
///    If `e` is a well-typed closed term and takes a step to `e'`
///    Then the type of the `e` is the same as the type of `e'`
let rec preservation (e:exp)
  : Lemma
    (requires
      Some? (typing empty e) /\
      Some? (step e))
    (ensures
      typing empty (Some?.v (step e)) == typing empty e)
  = match e with
    | EApp e1 e2 ->
      if is_value e1
      then if is_value e2
           then let EAbs x _ ebody = e1 in
                substitution_preserves_typing x ebody e2 empty
           else preservation e2
      else preservation e1

/// typed_step e:
///   Using progress and preservation, we can turn our partial, untyped
///   `step` function into a total `typed_step` whose type tells us that
///   – non-values always step
///   – and their type does not change
let typed_step 
    (e:exp {
      Some? (typing empty e) /\
      not(is_value e)
     })
  : e':exp{
     typing empty e' = typing empty e
    }
  = progress e; preservation e; Some?.v (step e)
