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

//SNIPPET_START: typ$
type typ =
  | TUnit : typ
  | TArr  : typ -> typ -> typ
//SNIPPET_END: typ$

//SNIPPET_START: exp$
let var = nat
type exp =
  | EUnit : exp
  | EVar  : var -> exp
  | ELam  : typ -> exp -> exp
  | EApp  : exp -> exp -> exp
//SNIPPET_END: exp$  


// Failed attempt

//SNIPPET_START: sub0$
let sub0 = var -> exp
//SNIPPET_END: sub0$

//SNIPPET_START: sub_beta0$
let sub_beta0 (e:exp)
  : sub0
  = fun (y:var) ->
        if y = 0 then e      (* substitute *)
        else EVar (y-1)    (* shift -1 *)
//SNIPPET_END: sub_beta0$

//SNIPPET_START: subst0$
let sub_inc0 : sub0 =  fun y -> EVar (y+1)

[@@expect_failure [19;19]]
let rec subst0 (s:sub0)
               (e:exp)
  : exp
  = match e with
    | EUnit -> EUnit
    | EVar x -> s x
    | EApp e1 e2 -> EApp (subst0 s e1) (subst0 s e2)
    | ELam t e1 -> ELam t (subst0 (sub_elam0 s) e1)

and sub_elam0 (s:sub0) 
  : sub0
  =  fun y ->
        if y=0
        then EVar y
        else subst0 sub_inc0 (s (y - 1))
//SNIPPET_END: subst0$


(* Parallel substitution operation `subst` *)

(* The termination argument uses a lexicographic ordering composed of:
   0) a bit saying whether the expression is a variable or not;
   1) an _undecidable_ well-founded order on substitutions that
      equates all renamings, equates all non-renamings, and makes
      renamings strictly smaller than non-renamings; we write down a
      non-constructive function is_renaming mapping substitutions
      (infinite objects) to 0 (renaming) or 1 (non-renaming)
   2) the structure of the expression e *)

//SNIPPET_START: sub$
let sub (renaming:bool) = 
    f:(var -> exp){ renaming <==> (forall x. EVar? (f x)) }
//SNIPPET_END: sub$

//SNIPPET_START: sub_inc$
let sub_inc 
  : sub true
  = fun y -> EVar (y+1)
//SNIPPET_END: sub_inc$

//SNIPPET_START: sub_beta$
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
//SNIPPET_END: sub_beta$

//SNIPPET_START: subst$
let bool_order (b:bool) = if b then 0 else 1
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
    | EUnit -> EUnit
    | EVar x -> s x
    | EApp e1 e2 -> EApp (subst s e1) (subst s e2)
    | ELam t e1 -> ELam t (subst (sub_elam s) e1)

and sub_elam (#r:bool) (s:sub r) 
  : Tot (sub r)
        (decreases %[1;
                     bool_order r;
                     0;
                     EVar 0])
  = let f : var -> exp = 
      fun y ->
        if y=0
        then EVar y
        else subst sub_inc (s (y - 1))
    in
    assert (not r ==> (forall x. ~(EVar? (s x)) ==> ~(EVar? (f (x + 1)))));
    f
//SNIPPET_END: subst$

//SNIPPET_START: subst1$
let rec subst1 (#r:bool)
              (s:sub r)
              (e:exp)
  : Tot (e':exp { r ==> (EVar? e <==> EVar? e') })
        (decreases %[bool_order r;
                     1;
                     e])
  = match e with
    | EVar x -> s x
    | ELam t e1 -> ELam t (subst1 (sub_elam1 s) e1)
    | EApp e1 e2 -> EApp (subst1 s e1) (subst1 s e2)
    | EUnit -> EUnit

and sub_elam1 (#r:bool) (s:sub r) 
  : Tot (sub r)
        (decreases %[bool_order r;
                     0;
                     EVar 0])
  = let f : var -> exp = 
      fun y ->
        if y=0
        then EVar y
        else match s (y - 1) with
             | EVar x -> sub_inc x
             | e -> subst1 sub_inc e
    in
    introduce not r ==> (exists x. ~ (EVar? (f x))) 
    with not_r. 
      eliminate exists y. ~ (EVar? (s y))
      returns _
      with not_evar_sy. 
        introduce exists x. ~(EVar? (f x))
        with (y + 1)
        and ()
    ;
    f
//SNIPPET_END: subst1$


//SNIPPET_START: step$
type step : exp -> exp -> Type =
  | Beta :
     t:typ ->
     e1:exp ->
     e2:exp ->
     step (EApp (ELam t e1) e2) (subst (sub_beta e2) e1)

  | AppLeft :
      #e1:exp ->
      e2:exp ->
      #e1':exp ->
      hst:step e1 e1' ->
      step (EApp e1 e2) (EApp e1' e2)

  | AppRight : 
      e1:exp ->
      #e2:exp ->
      #e2':exp ->
      hst:step e2 e2' ->
      step (EApp e1 e2) (EApp e1 e2')
//SNIPPET_END: step$

//SNIPPET_START: steps$
type steps : exp -> exp -> Type =
  | Single : #e0:exp ->
             #e1:exp ->
             step e0 e1 -> 
             steps e0 e1

  | Many  : #e0:exp ->
             #e1:exp ->
             #e2:exp -> 
             step e0 e1 ->
             steps e1 e2 -> 
             steps e0 e2
//SNIPPET_END: steps$

(* Type system; as inductive relation (not strictly necessary for STLC) *)

//SNIPPET_START: env$
let env = var -> option typ

let empty : env = fun _ -> None

let extend (t:typ) (g:env) 
  : env 
  = fun y -> if y = 0 then Some t
          else g (y-1)
//SNIPPET_END: env$

//SNIPPET_START: typing$
noeq 
type typing : env -> exp -> typ -> Type =
  | TyUnit :
      #g:env ->
      typing g EUnit TUnit

  | TyVar :
      #g:env ->
      x:var{Some? (g x)} ->
      typing g (EVar x) (Some?.v (g x))

  | TyLam :
      #g :env ->
      t:typ ->
      #e1:exp ->
      #t':typ ->
      hbody:typing (extend t g) e1 t' ->
      typing g (ELam t e1) (TArr t t')
            
  | TyApp :
      #g:env ->
      #e1:exp ->
      #e2:exp ->
      #t11:typ ->
      #t12:typ ->
      h1:typing g e1 (TArr t11 t12) ->
      h2:typing g e2 t11 ->
      typing g (EApp e1 e2) t12
//SNIPPET_END: typing$            

(* Progress *)

//SNIPPET_START: progress$
let is_value (e:exp) : bool = ELam? e || EUnit? e

let rec progress (#e:exp {~ (is_value e) })
                 (#t:typ)
                 (h:typing empty e t)
  : (e':exp & step e e')
  = let TyApp #g #e1 #e2 #t11 #t12 h1 h2 = h in
    match e1 with
    | ELam t e1' -> (| subst (sub_beta e2) e1', Beta t e1' e2 |)
    | _          -> let (| e1', h1' |) = progress h1 in
                   (| EApp e1' e2, AppLeft e2 h1'|)
//SNIPPET_END: progress$

(* Typing of substitutions (very easy, actually) *)

(* Substitution preserves typing
   Strongest possible statement; suggested by Steven Schäfer *)
//SNIPPET_START: substitution$
let subst_typing #r (s:sub r) (g1:env) (g2:env) =
    x:var{Some? (g1 x)} -> typing g2 (s x) (Some?.v (g1 x))

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
     | TyUnit -> TyUnit
     | TyVar x -> hs x
     | TyApp hfun harg -> TyApp (substitution s hfun hs) (substitution s harg hs)
     | TyLam tlam hbody ->
       let hs'' : subst_typing (sub_inc) g2 (extend tlam g2) =
         fun x -> TyVar (x+1) 
       in
       let hs' : subst_typing (sub_elam s) (extend tlam g1) (extend tlam g2) =
         fun y -> if y = 0 then TyVar y
               else substitution sub_inc (hs (y - 1)) hs''
       in
       TyLam tlam (substitution (sub_elam s) hbody hs')
//SNIPPET_END: substitution$

(* Substitution for beta reduction
   Now just a special case of substitution lemma *)
//SNIPPET_START: substitution_beta$
let substitution_beta #e #v #t_x #t #g 
                      (h1:typing g v t_x)
                      (h2:typing (extend t_x g) e t)
  : typing g (subst (sub_beta v) e) t
  = let hs : subst_typing (sub_beta v) (extend t_x g) g =
        fun y -> if y = 0 then h1 else TyVar (y-1) in
    substitution (sub_beta v) h2 hs
//SNIPPET_END: substitution_beta$

//SNIPPET_START: preservation_step$
let rec preservation_step #e #e' #g #t (ht:typing g e t) (hs:step e e') 
  : typing g e' t
  = let TyApp h1 h2 = ht in
    match hs with
    | Beta tx e1' e2' -> substitution_beta h2 (TyLam?.hbody h1)
    | AppLeft e2' hs1   -> TyApp (preservation_step h1 hs1) h2
    | AppRight e1' hs2   -> TyApp h1 (preservation_step h2 hs2)
//SNIPPET_END: preservation_step$

(* Multi-step preservation *)
//SNIPPET_START: preservation$
let rec preservation #e #e' #g #t (ht:typing g e t) (hs:steps e e') 
  : Tot (typing g e' t)
        (decreases hs)
  = match hs with
    | Single s -> 
      preservation_step ht s
    | Many s0 s1 -> 
      let ht' = preservation_step ht s0 in
      preservation ht' s1
//SNIPPET_END: preservation$

//SNIPPET_START: soundness_stmt$
let soundness #e #e' #t 
              (ht:typing empty e t) 
  : either (squash (is_value e))
           (e':exp & steps e e' & typing empty e' t)
//SNIPPET_END: soundness_stmt$
//SNIPPET_START: soundness_sol$
  = if is_value e then Inl ()
    else let (| e', s |) = progress ht in
         let ht' = preservation_step ht s in
         Inr (| e', Single s, ht' |)
//SNIPPET_END: soundness_sol$
