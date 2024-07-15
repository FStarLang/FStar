module Bug3207c

(* Minimization of Bug3207.fst *)

open FStar.Tactics
open FStar.Constructive
open FStar.Classical
open FStar.FunctionalExtensionality

(* Constructive-style progress and preservation proof for STLC with
   strong reduction, using deBruijn indices and parallel substitution. *)

type typ =
  | TArr    : typ -> typ -> typ
  | TSum    : typ -> typ -> typ
  | TPair   : typ -> typ -> typ
  | TUnit   : typ
  | TNat    : typ

type var = nat

open FStar.Bytes

type exp =
  | EVar         : var -> exp
  | EApp         : exp -> exp -> exp
  | ELam         : typ -> exp -> exp
  | EUnit        : exp
  | EZero        : exp
  | ESucc        : v:exp -> exp
  | ENRec        : exp -> exp -> exp -> exp
  | EInl         : v:exp -> exp
  | EInr         : v:exp -> exp
  | ECase        : exp -> exp -> exp -> exp
  | EFst         : exp -> exp
  | ESnd         : exp -> exp
  | EPair        : fst:exp -> snd:exp -> exp


(* Type system; as inductive relation (not strictly necessary for STLC) *)

type env = var -> Tot (option typ)

val empty : env
let empty _ = None

(* we only need extend at 0 *)
val extend : typ -> env -> Tot env
let extend t g y = if y = 0 then Some t
                   else g (y-1)

noeq type typing : env -> exp -> typ -> Type =
  | TyVar : #g:env ->
             x:var{Some? (g x)} ->
             typing g (EVar x) (Some?.v (g x))
  | TyLam : #g :env ->
             t :typ ->
            #e1:exp ->
            #t':typ ->
            $hbody:typing (extend t g) e1 t' ->
                   typing g (ELam t e1) (TArr t t')
  | TyApp : #g:env ->
            #e1:exp ->
            #e2:exp ->
            #t11:typ ->
            #t12:typ ->
            $h1:typing g e1 (TArr t11 t12) ->
            $h2:typing g e2 t11 ->
                typing g (EApp e1 e2) t12
  | TyUnit : #g:env ->
             typing g EUnit TUnit
  | TyZero : #g:env ->
             typing g EZero TNat
  | TySucc : #g:env ->
             #e:exp ->
             $h1:typing g e TNat ->
                 typing g (ESucc e) TNat
  | TyNRec : #g:env ->
             #e1:exp ->
             #e2:exp ->
             #e3:exp ->
             #t1:typ ->
             $h1:typing g e1 TNat ->
             $h2:typing g e2 t1 ->
             $h3:typing g e3 (TArr t1 t1) ->
                 typing g (ENRec e1 e2 e3) t1
  | TyInl  : #g:env ->
             #e:exp ->
             #t1:typ ->
             t2:typ ->
             $h1:typing g e t1 ->
                 typing g (EInl e) (TSum t1 t2)
  | TyInr  : #g:env ->
             #e:exp ->
             t1:typ ->
             #t2:typ ->
             $h1:typing g e t2 ->
                 typing g (EInr e) (TSum t1 t2)
  | TyCase : #g:env ->
             #e1:exp ->
             #e2:exp ->
             #e3:exp ->
             #t1:typ ->
             #t2:typ ->
             #t3:typ ->
             $h1:typing g e1 (TSum t1 t2) ->
             $h2:typing g e2 (TArr t1 t3) ->
             $h3:typing g e3 (TArr t2 t3) ->
                 typing g (ECase e1 e2 e3) t3
  | TyFst         : #g:env ->
                    #e:exp ->
                    #t1:typ ->
                    #t2:typ ->
                    $h1:typing g e (TPair t1 t2) ->
                        typing g (EFst e) t1
  | TySnd         : #g:env ->
                    #e:exp ->
                    #t1:typ ->
                    #t2:typ ->
                    $h1:typing g e (TPair t1 t2) ->
                        typing g (ESnd e) t2
  | TyPair        : #g:env ->
                    #e1:exp ->
                    #e2:exp ->
                    #t1:typ ->
                    #t2:typ ->
                    $h1:typing g e1 t1 ->
                    $h2:typing g e2 t2 ->
                        typing g (EPair e1 e2) (TPair t1 t2)

(* Parallel substitution operation `subst` *)
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
  | EZero -> EZero
  | ESucc e -> ESucc (subst s e)
  | ENRec e1 e2 e3 -> ENRec (subst s e1) (subst s e2) (subst s e3)
  | EInl e -> EInl (subst s e)
  | EInr e -> EInr (subst s e)
  | ECase e1 e2 e3 -> ECase (subst s e1) (subst s e2) (subst s e3)
  | EFst e -> EFst (subst s e)
  | ESnd e -> ESnd (subst s e)
  | EPair e1 e2 -> EPair (subst s e1) (subst s e2)

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
    introduce not r ==> (exists x. ~ (EVar? (f x)))
    with not_r. 
      eliminate exists y. ~ (EVar? (s y))
      returns (exists x. ~ (EVar? (f x)))
      with (not_evar_sy:squash (~(EVar? (s y)))). 
        introduce exists x. ~(EVar? (f x))
        with (y + 1)
        and ()
    ;
    f

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

let rec is_value (e:exp) : bool = 
     ELam? e || 
     EUnit? e || 
     EZero? e || 
     (ESucc? e && is_value (ESucc?.v e)) || 
     (EInl? e && is_value (EInl?.v e)) ||
     (EInr? e && is_value (EInr?.v e)) || 
     (EPair? e && is_value (EPair?.fst e) && is_value (EPair?.snd e) )

let progress (#e:exp { ~(is_value e) })
                 (#t:typ)
                 (h:typing empty e t)
  : e':exp & step e e'
  =  magic()

(* Typing of substitutions (very easy, actually) *)

(* Type preservation *)
let rec preservation_step #e #e' #g #t (ht:typing g e t) (hs:step e e') 
  : typing g e' t
  =  magic()
  
(** Phil Wadler: Progress + Preservation = Evaluation. **)
let rec eval (#e:exp) (#t:typ) (ht:typing empty e t)
  : Pure (e':exp & typing empty e' t)
     (requires True)
     (ensures (fun (| e', ht' |) -> is_value e'))
  =  if is_value e then (| e, ht |)
     else let (| e', st |) = progress ht in
          let ht' : typing empty e' t = preservation_step ht st in
          admit (); (** TODO: proof of termination required **)
          eval ht'

type wholeT = wt:exp & typing empty wt (TArr TUnit TNat)

let naive_rel_implies_c (wt : wholeT)  =
  let (| ew, htw |) = wt in
  calc (==) {
    eval (TyApp (dsnd (eval htw)) TyUnit);
  }
