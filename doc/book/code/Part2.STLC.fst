(*
   Copyright 2014-2015
     Simon Forest - Inria and ENS Paris
     Catalin Hritcu - Inria
     Nikhil Swamy - Microsoft Research

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

module Part2.STLC

(* Constructive-style progress and preservation proof for STLC with
   strong reduction, using deBruijn indices and parallel substitution. *)

type typ =
  | TArr  : typ -> typ -> typ
  | TUnit : typ

type var = nat

type exp =
  | EVar  : var -> exp
  | EApp  : exp -> exp -> exp
  | ELam  : typ -> exp -> exp
  | EUnit : exp

(* Parallel substitution operation `subst` *)

(* The termination argument uses a lexicographic ordering composed of:
   0) a bit saying whether the expression is a variable or not;
   1) an _undecidable_ well-founded order on substitutions that
      equates all renamings, equates all non-renamings, and makes
      renamings strictly smaller than non-renamings; we write down a
      non-constructive function is_renaming mapping substitutions
      (infinite objects) to 0 (renaming) or 1 (non-renaming)
   2) the structure of the expression e *)

let sub (renaming:bool) = 
    f:(var -> exp){ renaming <==> (forall x. EVar? (f x)) }

let bool_order (b:bool) = if b then 0 else 1

let sub_inc 
  : sub true
  = fun y -> EVar (y+1)

let is_var (e:exp) : int = if EVar? e then 0 else 1

let rec subst (#r:bool)
              (s:sub r)
              (e:exp)
  : Tot (e':exp { r ==> (EVar? e <==> EVar? e') })
        (decreases %[bool_order (EVar? e); 
                     bool_order r;
                     1;
                     e])
  = match e with
    | EVar x -> s x
    | ELam t e1 -> ELam t (subst (sub_elam s) e1)
    | EApp e1 e2 -> EApp (subst s e1) (subst s e2)
    | EUnit -> EUnit

and sub_elam (#r:bool) (s:sub r) 
  : Tot (sub r)
        (decreases %[1;
                     bool_order r;
                     0;
                     EVar 0])
  = fun y ->
      if y=0
      then EVar y
      else subst sub_inc (s (y - 1))

open FStar.Classical.Sugar

let sub_beta (e:exp)
  : sub (EVar? e)
  = let f = 
      fun (y:var) ->
        if y = 0 then e      (* substitute *)
        else (EVar (y-1))    (* shift -1 *)
    in
    if not (EVar? e)
    then introduce exists (x:var). ~(EVar? (f x))
         with 0 and ();
    f

(* Small-step operational semantics; strong / full-beta reduction is
   non-deterministic, so necessarily as inductive relation *)

type step : exp -> exp -> Type =
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp ->
            step (EApp (ELam t e1) e2) (subst (sub_beta e2) e1)

  | SApp1 : #e1:exp ->
             e2:exp ->
            #e1':exp ->
            hst:step e1 e1' ->
            step (EApp e1 e2) (EApp e1' e2)

  | SApp2 :  e1:exp ->
            #e2:exp ->
            #e2':exp ->
            hst:step e2 e2' ->
            step (EApp e1 e2) (EApp e1 e2')

  | SStrong : t:typ ->
              e:exp ->
              e':exp ->
              step e e' -> 
              step (ELam t e) (ELam t e')

  | STrans : #e0:exp ->
             #e1:exp ->
             #e2:exp -> 
             step e0 e1 ->
             step e1 e2 -> 
             step e0 e2
              
(* Type system; as inductive relation (not strictly necessary for STLC) *)

type env = var -> option typ

let empty : env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:typ) (g:env) 
  : env 
  = fun y -> if y = 0 then Some t
          else g (y-1)

noeq 
type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
             x:var{Some? (g x)} ->
             typing g (EVar x) (Some?.v (g x))

  | TyLam : #g :env ->
            t:typ ->
            #e1:exp ->
            #t':typ ->
            hbody:typing (extend t g) e1 t' ->
            typing g (ELam t e1) (TArr t t')
            
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:typ ->
            #t12:typ ->
            h1:typing g e1 (TArr t11 t12) ->
            h2:typing g e2 t11 ->
            typing g (EApp e1 e2) t12
            
  | TyUnit : #g:env ->
             typing g EUnit TUnit

(* Progress *)

let is_value (e:exp) : bool = ELam? e || EUnit? e

let rec progress (#e:exp {~ (is_value e) })
                 (#t:typ)
                 (h:typing empty e t)
  : (e':exp & step e e')
  = let TyApp #g #e1 #e2 #t11 #t12 h1 h2 = h in
    match e1 with
    | ELam t e1' -> (| subst (sub_beta e2) e1', SBeta t e1' e2 |)
    | _          -> let (| e1', h1' |) = progress h1 in
                   (| EApp e1' e2, SApp1 e2 h1'|)

(* Typing of substitutions (very easy, actually) *)
let subst_typing #r (s:sub r) (g1:env) (g2:env) =
    x:var{Some? (g1 x)} -> typing g2 (s x) (Some?.v (g1 x))

(* Substitution preserves typing
   Strongest possible statement; suggested by Steven Schäfer *)
let rec substitution (#g1:env) 
                     (#e:exp)
                     (#t:typ)
                     (#r:bool)
                     (s:sub r)
                     (#g2:env)
                     (h1:typing g1 e t)
                     (hs:subst_typing s g1 g2)
   : Tot (typing g2 (subst s e) t)
         (decreases %[bool_order (EVar? e); bool_order r; e])
   = match h1 with
   | TyVar x -> hs x
   | TyApp hfun harg -> TyApp (substitution s hfun hs) (substitution s harg hs)
   | TyLam tlam hbody ->
     let hs'' : subst_typing (sub_inc) g2 (extend tlam g2) =
       fun x -> TyVar (x+1) in
     let hs' : subst_typing (sub_elam s) (extend tlam g1) (extend tlam g2) =
       fun y -> if y = 0 then TyVar y
             else substitution sub_inc (hs (y - 1)) hs''
     in TyLam tlam (substitution (sub_elam s) hbody hs')
   | TyUnit -> TyUnit

(* Substitution for beta reduction
   Now just a special case of substitution lemma *)
let substitution_beta #e #v #t_x #t #g 
                      (h1:typing g v t_x)
                      (h2:typing (extend t_x g) e t)
  : typing g (subst (sub_beta v) e) t
  = let hs : subst_typing (sub_beta v) (extend t_x g) g =
        fun y -> if y = 0 then h1 else TyVar (y-1) in
    substitution (sub_beta v) h2 hs

(* Type preservation *)
let rec preservation #e #e' #g #t (ht:typing g e t) (hs:step e e') 
  : Tot (typing g e' t)
        (decreases hs)
  = match hs with
    | STrans s0 s1 ->
      let ht' = preservation ht s0 in
      preservation ht' s1
    | _ ->
      match ht with
      | TyApp h1 h2 -> (
        match hs with
        | SBeta tx e1' e2' -> substitution_beta h2 (TyLam?.hbody h1)
        | SApp1 e2' hs1   -> TyApp (preservation h1 hs1) h2
        | SApp2 e1' hs2   -> TyApp h1 (preservation h2 hs2)
      )
      | TyLam t hb ->
        let SStrong t e e' hs' = hs in
        let hb' = preservation hb hs' in
        TyLam t hb'

