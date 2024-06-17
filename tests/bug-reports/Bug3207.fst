module Bug3207

(* Based on file FStar/examples/metatheory/StlcStrongDbParSubst.fst *)

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
  | SBeta : t:typ ->
            e1:exp ->
            e2:exp ->
            step (EApp (ELam t e1) e2) (subst (sub_beta e2) e1)
  | SApp1 : #e1:exp ->
             e2:exp ->
            #e1':exp ->
            $hst:step e1 e1' ->
                 step (EApp e1 e2) (EApp e1' e2)
  | SApp2 :   e1:exp ->
             #e2:exp ->
            #e2':exp ->
            $hst:step e2 e2' ->
                 step (EApp e1 e2) (EApp e1 e2')
  | SSucc :    e:exp ->
             #e':exp ->
            $hst:step e e' ->
                 step (ESucc e) (ESucc e')     
  | SNRecV :  #e1:exp ->
             #e1':exp ->
               e2:exp ->
               e3:exp ->
             $hst:step e1 e1' ->
                 step (ENRec e1 e2 e3) (ENRec e1' e2 e3)
  | SNRec0 : e2:exp ->
             e3:exp ->
                 step (ENRec EZero e2 e3) e2
  | SNRecIter :  v:exp ->
                e2:exp ->
                e3:exp ->
                step (ENRec (ESucc v) e2 e3) (ENRec v (EApp e3 e2) e3)
  | SInl  :    e:exp ->
             #e':exp ->
            $hst:step e e' ->
                 step (EInl e) (EInl e')
  | SInr  :    e:exp ->
             #e':exp ->
            $hst:step e e' ->
                 step (EInr e) (EInr e')
  | SCase :  #e1:exp ->
            #e1':exp ->
              e2:exp ->
              e3:exp ->
            $hst:step e1 e1' ->
                 step (ECase e1 e2 e3) (ECase e1' e2 e3)
  | SCaseInl :  v:exp ->
               e2:exp ->
               e3:exp ->
                 step (ECase (EInl v) e2 e3) (EApp e2 v)
  | SCaseInr :  v:exp ->
               e2:exp ->
               e3:exp ->
                 step (ECase (EInr v) e2 e3) (EApp e3 v)
  | SFst0 :    #e:exp ->
              #e':exp ->
             $hst:step e e' ->
                 step (EFst e) (EFst e')
  | SFst :  e1:exp ->
            e2:exp ->
               step (EFst (EPair e1 e2)) e1
  | SSnd0 :    #e:exp ->
              #e':exp ->
             $hst:step e e' ->
                 step (ESnd e) (ESnd e')
  | SSnd :  e1:exp ->
            e2:exp ->
               step (ESnd (EPair e1 e2)) e2
  | SPair1  : #e1:exp ->
             #e1':exp ->
             $hst:step e1 e1' ->
               e2:exp ->
                 step (EPair e1 e2) (EPair e1' e2)
  | SPair2  :  e1:exp ->
              #e2:exp ->
             #e2':exp ->
             $hst:step e2 e2' ->
                 step (EPair e1 e2) (EPair e1 e2')


let rec is_value (e:exp) : bool = 
     ELam? e || 
     EUnit? e || 
     EZero? e || 
     (ESucc? e && is_value (ESucc?.v e)) || 
     (EInl? e && is_value (EInl?.v e)) ||
     (EInr? e && is_value (EInr?.v e)) || 
     (EPair? e && is_value (EPair?.fst e) && is_value (EPair?.snd e) )

let rec progress (#e:exp { ~(is_value e) })
                 (#t:typ)
                 (h:typing empty e t)
  : e':exp & step e e'
  =  match h with
     | TyApp #g #e1 #e2 #t11 #t12 h1 h2 -> 
     begin
          match e1 with
          | ELam t e1' -> (| subst (sub_beta e2) e1', SBeta t e1' e2 |)
          | _          -> let (| e1', h1' |) = progress h1 in
                              (| EApp e1' e2, SApp1 e2 h1'|) (** TODO: call-by-name **)
     end
     | TySucc #g #e h1 ->
          let (| e', h1' |) = progress h1 in
          (| ESucc e', SSucc e h1'|)
     | TyNRec #g #e1 #e2 #e3 #t1 h1 h2 h3 -> begin
          match e1 with
          | EZero -> (| e2, SNRec0 e2 e3 |)
          | ESucc v -> (| ENRec v (EApp e3 e2) e3, SNRecIter v e2 e3 |)
          | _ -> let (| e1', h1' |) = progress h1 in
                 (| ENRec e1' e2 e3, SNRecV e2 e3 h1' |)
     end
     | TyInl #g #e #t1 #t2 h1 -> 
          let (| e', h1' |) = progress h1 in
          (| EInl e', SInl e h1'|)
     | TyInr #g #e #t1 #t2 h1 -> 
          let (| e', h1' |) = progress h1 in
          (| EInr e', SInr e h1'|)
     | TyCase #g #e1 #e2 #e3 #t1 #t2 #t3 h1 h2 h3 -> begin
          match e1 with
          | EInl v -> (| EApp e2 v, SCaseInl v e2 e3 |)
          | EInr v -> (| EApp e3 v, SCaseInr v e2 e3 |)
          | _ ->
               let (| e1', h1' |) = progress h1 in
               (| ECase e1' e2 e3, SCase e2 e3 h1' |)
     end
     | TyFst #g #e #t1 #t2 h1 -> begin
          match e with
          | EPair e1 e2 -> (| e1, SFst e1 e2 |)
          | _ -> let (| e', h1' |) = progress h1 in
                 (| EFst e', SFst0 h1' |)
     end
     | TySnd #g #e #t1 #t2 h1 -> begin
          match e with
          | EPair e1 e2 -> (| e2, SSnd e1 e2 |)
          | _ -> let (| e', h1' |) = progress h1 in
                 (| ESnd e', SSnd0 h1' |)
     end
     | TyPair #g #e1 #e2 #t1 #t2 h1 h2 -> 
          if is_value e1 then
               let (| e2', h2' |) = progress h2 in
               (| EPair e1 e2', SPair2 e1 h2' |)
          else 
               let (| e1', h1' |) = progress h1 in
               (| EPair e1' e2, SPair1 h1' e2 |)


(* Typing of substitutions (very easy, actually) *)
let subst_typing #r (s:sub r) (g1:env) (g2:env) =
    x:var{Some? (g1 x)} -> typing g2 (s x) (Some?.v (g1 x))

(* Substitution preserves typing
   Strongest possible statement; suggested by Steven SchÃ¤fer *)
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
   | TyLam tlam hbody ->
     let hs'' : subst_typing (sub_inc) g2 (extend tlam g2) =
       fun x -> TyVar (x+1) in
     let hs' : subst_typing (sub_elam s) (extend tlam g1) (extend tlam g2) =
       fun y -> if y = 0 then TyVar y
             else substitution sub_inc (hs (y - 1)) hs''
     in TyLam tlam (substitution (sub_elam s) hbody hs')
      | TyApp hfun harg -> TyApp (substitution s hfun hs) (substitution s harg hs)
   | TyUnit -> TyUnit
   | TyZero -> TyZero
   | TySucc h1 -> TySucc (substitution s h1 hs)
   | TyNRec h1 h2 h3 -> TyNRec (substitution s h1 hs) (substitution s h2 hs) (substitution s h3 hs)
   | TyInl t2 h1 -> 
     let EInl e' = e in
     let hs' : typing g2 (EInl (subst s e')) t = TyInl t2 (substitution s h1 hs) in
     assert (subst s e == EInl (subst s e'));
     hs'
   | TyInr t1 h1 -> 
     let EInr e' = e in
     let hs' : typing g2 (EInr (subst s e')) t = TyInr t1 (substitution s h1 hs) in
     assert (subst s e == EInr (subst s e'));
     hs'
   | TyCase h1 h2 h3 -> TyCase (substitution s h1 hs) (substitution s h2 hs) (substitution s h3 hs)
   | TyFst h1 -> TyFst (substitution s h1 hs)
   | TySnd h1 -> TySnd (substitution s h1 hs)
   | TyPair h1 h2 -> TyPair (substitution s h1 hs) (substitution s h2 hs)

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
let rec preservation_step #e #e' #g #t (ht:typing g e t) (hs:step e e') 
  : typing g e' t
  =  match hs with
     | SBeta tx e1' e2' -> 
          let TyApp h1 h2 = ht in
          substitution_beta h2 (TyLam?.hbody h1)
     | SApp1 e2' hs1   -> 
          let TyApp h1 h2 = ht in
          TyApp (preservation_step h1 hs1) h2
     | SApp2 e1' hs2   -> 
          let TyApp h1 h2 = ht in
          TyApp h1 (preservation_step h2 hs2)
     | SSucc e' hs1    -> 
          let TySucc h1 = ht in
          TySucc (preservation_step h1 hs1)
     | SNRecV _ _ hs1 ->
          let TyNRec h1 h2 h3 = ht in
          TyNRec (preservation_step h1 hs1) h2 h3
     | SNRec0 _ _ ->
          let TyNRec h1 h2 h3 = ht in
          h2
     | SNRecIter _ _ _ ->
          let TyNRec h1 h2 h3 = ht in
          let TySucc h1' = h1 in
          TyNRec h1' (TyApp h3 h2) h3
     | SInl _ hs1     -> 
          let TyInl t2 h1 = ht in
          TyInl t2 (preservation_step h1 hs1)
     | SInr _ hs1     -> 
          let TyInr t1 h1 = ht in
          TyInr t1 (preservation_step h1 hs1)
     | SCase _ _ hs1 -> 
          let TyCase h1 h2 h3 = ht in
          TyCase (preservation_step h1 hs1) h2 h3
     | SCaseInl _ _ _ -> 
          let TyCase h1 h2 h3 = ht in
          let TyInl _ h1' = h1 in
          TyApp h2 h1'
     | SCaseInr _ _ _ -> 
          let TyCase h1 h2 h3 = ht in
          let TyInr _ h1' = h1 in
          TyApp h3 h1'
     | SFst0 hs1 -> 
          let TyFst h1 = ht in
          TyFst (preservation_step h1 hs1)
     | SFst _ _ -> 
          let TyFst h1 = ht in
          let TyPair h1' _ = h1 in
          h1'
     | SSnd0 hs1 -> 
          let TySnd h1 = ht in
          TySnd (preservation_step h1 hs1)
     | SSnd _ _ -> 
          let TySnd h1 = ht in
          let TyPair _ h1' = h1 in
          h1'
     | SPair1 hs1 _ ->
          let TyPair h1 h2 = ht in
          TyPair (preservation_step h1 hs1) h2
     | SPair2 _ hs2 ->
          let TyPair h1 h2 = ht in
          TyPair h1 (preservation_step h2 hs2)

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

(** *** Elaboration of types and expressions to F* *)

open FStar.Ghost
open FStar.UInt32
let convert (n : nat) : u32 = if n < 65535 then (uint_to_t n <: u32) else 0ul

type file_descr = int

let rec elab_typ (t:typ) : Type =
  match t with
  | TArr t1 t2 -> (elab_typ t1) -> Tot (elab_typ t2)
  | TUnit -> unit
  | TNat -> nat
  | TSum t1 t2 -> either (elab_typ t1) (elab_typ t2)
  | TPair t1 t2 -> (elab_typ t1) & (elab_typ t2)

type venv (g:env) = x:var{Some? (g x)} -> elab_typ (Some?.v (g x))

let vempty : venv empty = fun _ -> assert false

let vextend #t (x:elab_typ t) (#g:env) (ve:venv g) : venv (extend t g) =
  fun y -> if y = 0 then x else ve (y-1)

let cast_TArr #t1 #t2 (h : (elab_typ t1 -> Tot (elab_typ t2))) : elab_typ (TArr t1 t2) = h

open FStar.List.Tot

let rec elab_exp (#g:env) (#e:exp) (#t:typ) (h:typing g e t) (ve:venv g)
  : Tot (elab_typ t) (decreases e) =
  match e with
  | EUnit -> ()
  | EZero -> 0
  | ESucc e ->
       let TySucc h1 = h in
       assert (t == TNat);
       let v = elab_exp h1 ve in
       v
  | ENRec e1 e2 e3 ->
       let TyNRec h1 h2 h3 = h in
       let v1 = elab_exp h1 ve in
       let v2 : elab_typ t = elab_exp h2 ve in
       let v3 : elab_typ (TArr t t) = elab_exp h3 ve in
       let rec f (n : nat) : Tot (elab_typ t) =
         if n = 0 then v2 else f (n - 1) in
       f v1
  | EInl e ->
       let TyInl #_ #_ #t1 #t2 h1 = h in
       let v = elab_exp h1 ve in
       Inl #(elab_typ t1) #(elab_typ t2) v
  | EInr e ->
       let TyInr #_ #_ #t1 #t2 h1 = h in
       let v = elab_exp h1 ve in
       Inr #(elab_typ t1) #(elab_typ t2) v
  | ECase e1 e2 e3 ->
       let TyCase #_ #_ #_ #_ #t1 #t2 #t3 h1 h2 h3 = h in
       let v1 = elab_exp h1 ve in
       let v2 = elab_exp h2 ve in
       let v3 = elab_exp h3 ve in
       (match v1 with | Inl x -> v2 x | Inr y -> v3 y)
  | EVar x -> ve x
  | ELam t1 e1 ->
       let TyLam t1' #_ #t2 h1 = h in
       assert (t1' == t1);
       assert (t == TArr t1 t2);
       let w : elab_typ t1 -> Tot (elab_typ t2) =
         (fun x -> elab_exp h1 (vextend x ve)) in
       cast_TArr w
  | EApp e1 e2 ->
       let TyApp #_ #_ #_ #t1 #t2 h1 h2 = h in
       assert ((elab_typ t) == (elab_typ t2));
       (* TODO: Should we change the order here, first evaluate argument? *)
       let v1 : elab_typ (TArr t1 t2) = elab_exp h1 ve in
       let v2 : elab_typ t1 = elab_exp h2 ve in
       v1 v2
  | EFst e ->
       let TyFst #_ #_ #t1 #t2 h1 = h in
       let v = elab_exp h1 ve in
       fst #(elab_typ t1) #(elab_typ t2) v
  | ESnd e ->
       let TySnd #_ #_ #t1 #t2 h1 = h in
       let v = elab_exp h1 ve in
       snd #(elab_typ t1) #(elab_typ t2) v
  | EPair e1 e2 ->
       let TyPair #_ #_ #_ #t1 #t2 h1 h2 = h in
       let v1 = elab_exp h1 ve in
       let v2 = elab_exp h2 ve in
       (v1, v2)

(** ** Semantics **)
let sem #t (#e:exp) (hte:typing empty e t) : elab_typ t = 
     let (| e', hte' |) = eval hte in
     elab_exp hte' vempty

type wholeS = (unit -> Tot nat)
val behS : wholeS -> nat
let behS ws = ws ()

type wholeT = wt:exp & typing empty wt (TArr TUnit TNat)

val behT : wt:wholeT -> nat 
let behT (| ew, htw |) = sem (TyApp htw TyUnit)

type rel = 
  #ty:typ -> 
  elab_typ ty ->             (** F* value **)
  #e:exp ->                  (** STLC value **)
  typing empty e ty -> 
  Type0

let rel_whole (r:rel) (ws:wholeS) (wt:wholeT) : Type0 =
  ws `r` (dsnd wt) ==> behS ws == behT wt

val naive_rel : rel
let rec naive_rel #ty fst_e hte =
  let (| stlc_e, hte |) = eval hte in
  match hte with
  | TyLam tv #_ #t' _ -> 
    let fst_f : elab_typ tv -> elab_typ t' = fst_e in
    forall (v:exp) (htv:typing empty v tv). 
      let fst_v : elab_typ tv = elab_exp htv vempty in
      let happ : typing empty (EApp stlc_e v) t' = TyApp hte htv in
      (fst_v `naive_rel` htv) <==> ((fst_f fst_v) `naive_rel` happ)
  | TyUnit -> fst_e == ()
  | TyZero -> fst_e == 0
  | TySucc hte' -> fst_e > 0 /\ (fst_e-1) `naive_rel` hte'
  | TyInl #_ #_ #t1 t2 ht1 ->
    let fst_sum : either (elab_typ t1) (elab_typ t2) = fst_e in
    Inl? fst_sum /\ (Inl?.v fst_sum `naive_rel` ht1)
  | TyInr #_ #_ t1 #t2 ht2 ->
    let fst_sum : either (elab_typ t1) (elab_typ t2) = fst_e in
    Inr? fst_sum /\ (Inr?.v fst_sum `naive_rel` ht2)
  | TyPair #_ #_ #_ #t1 #t2 ht1 ht2 ->
    let fst_pair : (elab_typ t1 & elab_typ t2) = fst_e in
    let (fst_fst, fst_snd) = fst_pair in
    (fst_fst `naive_rel` ht1) /\ (fst_snd `naive_rel` ht2)

let naive_rel_implies_c ws wt : Lemma (rel_whole naive_rel ws wt) = 
  let (| ew, htw |) = wt in
  introduce 
    ws `naive_rel` (dsnd wt)
  ==> 
    behS ws == behT wt
  with _. begin
    let (| ew', htw' |) = eval (dsnd wt) in
    assert (TyLam? htw');
    let htapp : typing empty (EApp ew' EUnit) TNat = TyApp htw' TyUnit in
    assert (() `naive_rel` TyUnit);
    assert ((ws ()) `naive_rel` htapp);
    let (| ev, htv |) = eval htapp in
    match htv with
    | TyZero -> begin
      calc (==) {
        behS ws;
        == { _ by (tadmit ()) }
        elab_exp (dsnd (eval (TyApp (dsnd (eval htw)) TyUnit))) vempty;
        == { _ by (tadmit ()) }
        behT wt;
      }
    end
    | TySucc htapp' -> admit ()
  end
