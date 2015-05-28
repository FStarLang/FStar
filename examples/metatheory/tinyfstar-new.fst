(*--build-config
    options:--z3timeout 15 --log_types --max_fuel 4 --max_ifuel 4 --initial_fuel 4 --initial_ifuel 2;
    other-files:../../lib/classical.fst ../../lib/ext.fst
  --*)
module TinyFStarNew

open Classical
open FunctionalExtensionality

type var = nat
type loc = nat

type heap = loc -> Tot int


type eff =
  | EfPure
  | EfAll


type econst =
  | EcUnit
  | EcInt : i:int -> econst
  | EcLoc : l:loc -> econst
  | EcBang
  | EcAssign
  | EcSel
  | EcUpd
  | EcHeap : h:heap -> econst
  | EcFixPure : tx:typ -> t':typ -> t'':typ -> wp:typ -> econst
  | EcFixOmega : tx:typ -> t':typ -> wp:typ -> econst

and tconst =
  | TcUnit
  | TcInt
  | TcRefInt
  | TcHeap

  | TcFalse
  | TcAnd

  | TcForallE
  | TcForallT : k:knd -> tconst

  | TcEqE
  | TcEqT     : k:knd -> tconst

  | TcPrecedes

and knd =
  | KType : knd
  | KKArr : karg:knd -> kres:knd -> knd
  | KTArr : targ:typ -> kres:knd -> knd

and typ =
  | TVar   : a:var -> typ
  | TConst : c:tconst -> typ

  | TArr  : t:typ -> c:cmp -> typ
  | TTLam : k:knd -> tbody:typ -> typ
  | TELam : t:typ -> ebody:typ -> typ
  | TTApp : t1:typ -> t2:typ -> typ
  | TEApp : t:typ -> e:exp -> typ

and exp =
  | EVar : x:var -> exp
  | EConst : c:econst -> exp
  | ELam : t:typ -> ebody:exp -> exp
  | EIf0 : eguard:exp -> ethen:exp -> eelse:exp -> exp
  | EApp : e1:exp -> e2:exp -> exp

and cmp =
  | Cmp :  m:eff -> t:typ -> wp:typ -> cmp

(****************************)
(* Sugar                    *)
(****************************)

let eunit = EConst EcUnit
let eint x = EConst (EcInt x)
let eloc l = EConst (EcLoc l)
let ebang el = EApp (EConst EcBang) el
let eassign el ei = EApp (EApp (EConst EcAssign) el) ei
let esel eh el = EApp (EApp (EConst EcSel) eh) el
let eupd eh el ei = EApp (EApp (EApp (EConst EcUpd) eh) el) ei
let eheap h = EConst (EcHeap h)

let tunit = TConst TcUnit
let tint = TConst TcInt
let tref = TConst TcRefInt
let theap = TConst TcHeap
(*
        fix_pure : tx:Type -> t':(tx->Type) -> t'':(tx->Type) ->
                   wp:(x:tx->K_PURE(t'' x)) -> d:(x:tx -> Tot (t' x)) ->
                   F:(x:tx -> f: (y:tx -> PURE (t'' y)
                                 (up_PURE (precedes (d y) (d x)) /\_PURE (wp y)))
                           -> PURE (t'' x) (wp x)) ->
                   Tot t  (where t = y:tx -> PURE (t'' y) (wp y))

       fix_omega : tx:Type -> t':(tx->Type) -> wp:(x:tx->K_ALL(t' x)) ->
                   F:(x:tx -> f:t -> ALL (t' x) (wp x)) -> Tot t
                               (where t = y:tx -> ALL (t' y) (wp y))
*)
(*
let tfixpure = TTLam (KType) (*tx*)(
                  TTLam (KTArr (TVar 0) KType) (*t'*)(
                   TTLam (KTArr (TVar 1) KType) (*t''*)(                  
		     TTLam (KTArr (TVar 2) (k_m (EfPure) (TEApp (TVar 0) (EVar 0)))) (*wp*)(
*)

let tfalse = TConst TcFalse
let tand  a b = TTApp (TTApp (TConst TcAnd) a) b

let tforalle t p = TTApp (TTApp (TConst TcForallE) t) (TELam t p)
let tforallt k p = TTApp (TConst (TcForallT k)) (TTLam k p)

let teqe e1 e2 = TEApp (TEApp (TConst TcEqE) e1) e2
let teqt k t1 t2 = TTApp (TTApp (TConst (TcForallT k)) t1) t2
let teqtype = teqt KType

let tprecedes e1 e2 = TEApp (TEApp (TConst TcPrecedes) e1) e2

(*TODO:write a function {e|t|k}shift_up which
shift both expression and type variables
and prove some properties on it*)

(****************************)
(* Expression Substitutions *)
(****************************)

(* CH: My impression is that pairing up substitutions and having a
       single set of operations for substituting would be better.
       We can return to this later though. *)

type esub = var -> Tot exp

opaque type erenaming (s:esub) = (forall (x:var). is_EVar (s x))

val is_erenaming : s:esub -> Tot (n:int{(  erenaming s  ==> n=0) /\
                                        (~(erenaming s) ==> n=1)})
let is_erenaming s = (if excluded_middle (erenaming s) then 0 else 1)

val esub_id : esub
let esub_id = fun x -> EVar x

val esub_inc_gen : nat -> var -> Tot exp
let esub_inc_gen x y = EVar (y+x)

val esub_dec : var -> Tot exp
let esub_dec x = if x = 0 then EVar 0 else EVar (x-1)

val esub_inc : var -> Tot exp
let esub_inc = esub_inc_gen 1

val esub_inc2 : var -> Tot exp
let esub_inc2 = esub_inc_gen 2

let is_evar (e:exp) : int = if is_EVar e then 0 else 1

val omap : ('a -> Tot 'b) -> option 'a -> Tot (option 'b)
let omap f o =
  match o with
  | Some x -> Some (f x)
  | None   -> None

(****************************)
(*   Type   Substitutions   *)
(****************************)

type tsub = var -> Tot typ
opaque type trenaming (s:tsub) = (forall (x:var). is_TVar (s x))

val is_trenaming : s:tsub -> Tot (n:int{(  trenaming s  ==> n=0) /\
                                        (~(trenaming s) ==> n=1)})
let is_trenaming s = (if excluded_middle (trenaming s) then 0 else 1)

val tsub_inc_above : nat -> var -> Tot typ
let tsub_inc_above x y = if y<x then TVar y else TVar (y+1)

val tsub_dec : var -> Tot typ
let tsub_dec x = if x = 0 then TVar 0 else TVar (x-1)

val tsub_id :tsub
let tsub_id = fun x -> TVar x

val tsub_inc : var -> Tot typ
let tsub_inc = tsub_inc_above 0

let is_tvar (t:typ) : int = if is_TVar t then 0 else 1

(********************************)
(* Global substitution function *)
(********************************)

(*The projectors for pairs were not working well with substitutions*)
type sub =
| Sub : es:esub -> ts:tsub -> sub

opaque type renaming (s:sub) = (erenaming (Sub.es s))  /\ (trenaming (Sub.ts s))

val is_renaming : s:sub -> Tot (n:int{(  renaming s  ==> n=0) /\
                                       (~(renaming s) ==> n=1)})
let is_renaming s = (if excluded_middle (renaming s) then 0 else 1)

let sub_einc_gen y = Sub (esub_inc_gen y) tsub_id
let sub_einc = sub_einc_gen 1
let sub_edec = Sub esub_dec tsub_id
let sub_tinc = Sub esub_id tsub_inc
let sub_tdec = Sub esub_id tsub_dec
let sub_id = Sub esub_id tsub_id

val esubst : s:sub -> e:exp -> Pure exp (requires True)
      (ensures (fun e' -> renaming s /\ is_EVar e ==> is_EVar e'))
      (decreases %[is_evar e; is_renaming s;1; e])
val ecsubst : s:sub -> ec:econst -> Tot econst
      (decreases %[1; is_renaming s; 1; ec])
val tsubst : s:sub -> t:typ -> Pure typ (requires True)
      (ensures (fun t' -> renaming s /\ is_TVar t ==> is_TVar t'))
      (decreases %[is_tvar t; is_renaming s;1; t])
val tcsubst : s:sub -> tc: tconst -> Tot tconst
      (decreases %[1; is_renaming s; 1; tc])
val csubst : s:sub -> c:cmp -> Tot cmp
      (decreases %[1; is_renaming s; 1; c])
val ksubst : s:sub -> k:knd -> Tot knd
      (decreases %[1; is_renaming s; 1; k])
val sub_elam : s:sub -> Tot (r:sub{renaming s ==> renaming r})
      (decreases %[1; is_renaming s; 0; EVar 0])
val sub_tlam : s:sub -> Tot(r:sub{renaming s ==> renaming r})
      (decreases %[1; is_renaming s; 0; EVar 0])

let rec sub_elam s =
let esub_elam : x:var -> Tot(e:exp{renaming s ==> is_EVar e}) =
  fun x -> if x = 0 then EVar x
           else esubst sub_einc (Sub.es s (x-1))
  in
let tsub_elam : x:var -> Tot(t:typ{renaming s ==> is_TVar t}) =
  fun a -> tsubst sub_einc (Sub.ts s a)
  in
Sub esub_elam tsub_elam
and sub_tlam s =
let esub_tlam : x:var -> Tot(e:exp{renaming s ==> is_EVar e}) =
   fun x -> esubst sub_tinc (Sub.es s x)
in
let tsub_tlam : a:var -> Tot(t:typ{renaming s ==> is_TVar t}) =
   fun a -> if a = 0 then TVar a
            else tsubst sub_tinc (Sub.ts s (a-1))
in
Sub esub_tlam tsub_tlam


(*Substitution inside expressions*)
and esubst s e =
  match e with
  | EVar x -> Sub.es s x
  | EConst ec -> EConst (ecsubst s ec)
  | ELam t ebody -> ELam (tsubst s t) (esubst (sub_elam s) ebody)
  | EIf0 g ethen eelse -> EIf0 (esubst s g) (esubst s ethen) (esubst s eelse)
  | EApp e1 e2 -> EApp (esubst s e1) (esubst s e2)
(*Substitution inside expression constants*)
and ecsubst s ec =
  match ec with
  | EcFixPure tx t' t'' wp -> EcFixPure (tsubst s tx) (tsubst s t') (tsubst s t'') (tsubst s wp)
  | EcFixOmega tx t' wp -> EcFixOmega (tsubst s tx) (tsubst s t') (tsubst s wp)
  | _ -> ec
(*Substitution inside types*)
and tsubst s t =
  match t with
  | TVar a -> (Sub.ts s a)
  | TConst c -> TConst (tcsubst s c)
  | TArr t c ->
     TArr (tsubst s t)
          (csubst (sub_elam s) c)
  | TTLam k tbody ->
     TTLam (ksubst s k) (tsubst (sub_tlam s) tbody)
  | TELam t tbody ->
     TELam (tsubst s t) (tsubst (sub_elam s) tbody)
  | TTApp t1 t2 -> TTApp (tsubst s t1) (tsubst s t2)
  | TEApp t e -> TEApp (tsubst s t) (esubst s e)
and tcsubst s tc = match tc with
| TcEqT k -> TcEqT (ksubst s k)
| TcForallT k -> TcForallT (ksubst s k)
| _ -> tc
and csubst s c = let Cmp m t wp = c in
Cmp m (tsubst s t) (tsubst s wp)
(*Substitution inside kinds*)
and ksubst s k =
  match k with
  | KType -> KType
  | KKArr k kbody ->
     KKArr (ksubst s k) (ksubst (sub_tlam s) kbody)
  | KTArr t kbody ->
     (KTArr (tsubst s t) (ksubst (sub_elam s) kbody))

val esub_elam_at0 : s:sub -> Lemma (Sub.es (sub_elam s) 0 = EVar 0)
let esub_elam_at0 s = ()
(*BUG : without this normally neutral code, the file does not compile -> ??? *)
let plouf s t1 ebody = assert (sub_elam s == sub_elam s)
val etsubst : s:tsub -> e:exp -> Tot exp
let etsubst s e = esubst (Sub esub_id s) e

val ttsubst : s:tsub -> t:typ -> Tot typ
let ttsubst s t = tsubst (Sub esub_id s) t

val ktsubst : s:tsub -> k:knd -> Tot knd
let ktsubst s k = ksubst (Sub esub_id s) k

val eesubst : s:esub -> e:exp -> Tot exp
val tesubst : s:esub -> t:typ -> Tot typ
val kesubst : s:esub -> k:knd -> Tot knd

(*SF : it is better to avoid these functions that build new substitutions*)
let eesubst s e = esubst (Sub s tsub_id) e

let tesubst s t = tsubst (Sub s tsub_id) t

let kesubst s k = ksubst (Sub s tsub_id) k

(* Beta substitution for expressions *)

val esub_ebeta_gen : var -> exp -> Tot esub
let esub_ebeta_gen x e = fun y -> if y < x then (EVar y)
                                 else if y = x then e
                                 else (EVar (y-1))
val esub_ebeta : exp -> Tot esub
let esub_ebeta = esub_ebeta_gen 0

val sub_ebeta : exp -> Tot sub
let sub_ebeta e = Sub (esub_ebeta e) (tsub_id)

val esubst_ebeta : exp -> exp -> Tot exp
let esubst_ebeta e = esubst (sub_ebeta e)

val tsubst_ebeta : exp -> typ -> Tot typ
let tsubst_ebeta e = tsubst (sub_ebeta e)

val ksubst_ebeta : exp -> knd -> Tot knd
let ksubst_ebeta e = ksubst (sub_ebeta e)

let eesh = esubst sub_einc
let cesh = csubst sub_einc
let tesh = tsubst sub_einc
let kesh = ksubst sub_einc

let eeshd = esubst sub_edec
let ceshd = csubst sub_edec
let teshd = tsubst sub_edec
let keshd = ksubst sub_edec
(* Beta substitution for types *)
val tsub_tbeta_gen : var -> typ -> Tot tsub
let tsub_tbeta_gen x t = fun y -> if y < x then (TVar y)
                                 else if y = x then t
                                 else (TVar (y-1))
val tsub_tbeta : typ -> Tot tsub
let tsub_tbeta = tsub_tbeta_gen 0

val sub_tbeta : typ -> Tot sub
let sub_tbeta t = Sub (esub_id) (tsub_tbeta t)

val esubst_tbeta : typ -> exp -> Tot exp
let esubst_tbeta t = esubst (sub_tbeta t)

val tsubst_tbeta : typ -> typ -> Tot typ
let tsubst_tbeta t = tsubst (sub_tbeta t)

val ksubst_tbeta : typ -> knd -> Tot knd
let ksubst_tbeta t = ksubst (sub_tbeta t)


let etsh = esubst sub_tinc
let ttsh = tsubst sub_tinc
let ktsh = ksubst sub_tinc

let etshd = esubst sub_tdec
let ttshd = tsubst sub_tdec
let ktshd = ksubst sub_tdec

val ksubst_with_sub_id : k:knd -> Lemma (ksubst sub_id k = k)
let ksubst_with_sub_id k = admit()

val tsubst_with_sub_id : t:typ -> Lemma (tsubst sub_id t = t)
let tsubst_with_sub_id t = admit()


(********************************)
(* Composition of substitutions *)
(********************************)

val sub_comp : s1:sub -> s2:sub -> Tot sub
let sub_comp s1 s2 =
Sub (fun x -> esubst s1 (Sub.es s2 x)) (fun a -> tsubst s1 (Sub.ts s2 a))

val sub_elam_comp : s1:sub -> s2:sub -> Lemma (sub_comp (sub_elam s1) (sub_elam s2) = sub_elam (sub_comp s1 s2))
let sub_elam_comp s1 s2 = admit()

val esubst_comp : s1:sub -> s2:sub -> e:exp -> Lemma (esubst s1 (esubst s2 e) = esubst (sub_comp s1 s2) e)
(decreases %[e])
val tsubst_comp : s1:sub -> s2:sub -> t:typ -> Lemma (tsubst s1 (tsubst s2 t) = tsubst (sub_comp s1 s2) t)
(decreases %[t])
val ksubst_comp : s1:sub -> s2:sub -> k:knd -> Lemma (ksubst s1 (ksubst s2 k) = ksubst (sub_comp s1 s2) k)
(decreases %[k])

let rec esubst_comp s1 s2 e = match e with
| EVar x -> ()
| EConst ec -> admit()
| ELam t ebody -> 
(
 tsubst_comp s1 s2 t; 
 esubst_comp (sub_elam s1) (sub_elam s2) ebody;
 sub_elam_comp s1 s2
)
| _ -> admit()
and tsubst_comp s1 s2 t = admit()
and ksubst_comp s1 s2 k = admit()
type sub_equal (s1:sub) (s2:sub) = (FEq (Sub.es s1) (Sub.es s2) /\ FEq (Sub.ts s1) (Sub.ts s2) )

val sub_ext : s1:sub -> s2:sub{sub_equal s1 s2} -> Lemma(s1 = s2)
let sub_ext s1 s2 = ()

val edec_einc_comp : unit -> Lemma ((sub_comp sub_edec sub_einc) = sub_id)
let edec_einc_comp () = sub_ext (sub_comp sub_edec sub_einc) sub_id

val tdec_tinc_comp : unit -> Lemma ((sub_comp sub_tdec sub_tinc) = sub_id)
let tdec_tinc_comp () = sub_ext (sub_comp sub_tdec sub_tinc) sub_id


val teshd_tesh : t:typ -> Lemma (teshd (tesh t) = t)
let teshd_tesh t = admit()

val tesh_ttsh : t:typ -> Lemma (tesh (ttsh t) = ttsh (tesh t))
let tesh_ttsh t = admit()

val tesh_ttshd : t:typ -> Lemma (tesh (ttshd t) = ttshd (tesh t))
let tesh_ttshd t = admit()

val ttshd_ttsh : t:typ -> Lemma (ttshd (ttsh t) = t)
let ttshd_ttsh t = admit()

val kesh_ktsh : k:knd -> Lemma (kesh (ktsh k) = ktsh (kesh k))
let kesh_ktsh k = admit()

val keshd_ktsh : k:knd -> Lemma (keshd (ktsh k) = ktsh (keshd k))
let keshd_ktsh k = admit()

val keshd_kesh : k:knd -> Lemma (keshd (kesh k) = k)
let keshd_kesh k = admit()

val ktshd_ktsh : k:knd -> Lemma (ktshd (ktsh k) = k)
let ktshd_ktsh k = admit()
(****************************)
(* Derived logic constants  *)
(****************************)

let timpl t1 t2 = tforalle t1 (tesh t2)
let tnot t = timpl t tfalse
let ttrue = tnot tfalse
let tor t1 t2 = timpl (tnot t1) t2

(*************************************)
(*   Common substitution functions   *)
(*************************************)
(*TODO:Settle down the substitution strategy*)
(*
val eshift_up_above : ei:nat -> ti:nat ->
                      eplus:nat -> tplus:nat ->
                      e:exp -> Tot exp
val tshift_up_above : ei:nat -> ti:nat ->
                      eplus:nat -> tplus:nat ->
                      t:typ -> Tot typ
val kshift_up_above : ei:nat -> ti:nat ->
                      eplus:nat -> tplus:nat ->
                      t:typ -> Tot typ
*)

(***********************)
(*  Heap manipulation  *)
(***********************)

val upd_heap : l:loc -> i:int -> h:heap -> Tot heap
let upd_heap l i h =
  fun x -> if x = l then i else h x

(********************************************)
(* Reduction for types and pure expressions *)
(********************************************)

val is_value : exp -> Tot bool
let rec is_value e =
  match e with
  | EConst _
  | ELam _ _ -> true
  | EVar _
  | EIf0 _ _ _ -> false
  | EApp e1 e2 -> is_value e2 &&
      (match e1 with
       | EApp e11 e12 -> is_value e12 &&
         (match e11 with
          | EApp (EConst c) e112 -> is_EcUpd c && is_value e112
          | EConst c             -> is_EcUpd c || is_EcSel c
          | _ -> false)
       | EConst c -> is_EcUpd c || is_EcSel c || is_EcAssign c || is_EcHeap c
       | _ -> false)

type value = e:exp{is_value e}

type tstep : typ -> typ -> Type =
  | TsEBeta : tx:typ ->
              t:typ ->
              e:exp ->
              tstep (TEApp (TELam tx t) e) (tsubst_ebeta e t)
  | TsTBeta : k:knd ->
              t:typ ->
              t':typ ->
              tstep (TTApp (TTLam k t) t') (tsubst_tbeta t' t)
  | TsArrT1 : #t1:typ->
              #t1':typ->
              c:cmp ->
              =ht:tstep t1 t1' ->
              tstep (TArr t1 c) (TArr t1' c)
  | TsTAppT1 : #t1:typ ->
               #t1':typ ->
               t2 : typ ->
               =ht:tstep t1 t1' ->
               tstep (TTApp t1 t2) (TTApp t1' t2)
  | TsTAppT2 : t1:typ ->
               #t2:typ ->
               #t2':typ ->
               =ht:tstep t2 t2' ->
               tstep (TTApp t1 t2) (TTApp t1 t2')
  | TsEAppT : #t:typ ->
              #t':typ ->
              e:exp ->
              =ht:tstep t t' ->
              tstep (TEApp t e) (TEApp t' e)
  | TsEAppE : t:typ ->
              #e:exp ->
              #e':exp ->
              =he:epstep e e' ->
              tstep (TEApp t e) (TEApp t e')
  | TsTLamT : k:knd ->
              #t:typ ->
              #t':typ ->
              =ht:tstep t t' ->
              tstep (TTLam k t) (TTLam k t')
  | TsELamT1 : #t1:typ ->
               #t1':typ ->
               t2:typ ->
               =ht:tstep t1 t1' ->
               tstep (TELam t1 t2) (TELam t1' t2)
(*Why do the last two rules reduce different part of the term ?
  Why do we have TTLam k t ~> TTLam k t' and not TELam t1 t2 ~> TELam t1 t2' ? *)
and epstep : exp -> exp -> Type =
  | PsBeta :  t:typ ->
              ebody:exp ->
              v:value ->
              epstep (EApp (ELam t ebody) v) (esubst_ebeta v ebody)
  | PsIf0 :  e1:exp ->
             e2:exp ->
             epstep (EIf0 (eint 0) e1 e2) e1
  | PsIfS :  i:int{i<>0} ->
             e1:exp ->
             e2:exp ->
             epstep (EIf0 (eint i) e1 e2) e2
  | PsAppE1 : #e1:exp ->
              #e1':exp ->
              e2:exp ->
              =ht:epstep e1 e1' ->
              epstep (EApp e1 e2) (EApp e1' e2)
  | PsAppE2 : e1:exp ->
              #e2:exp ->
              #e2':exp ->
              =ht:epstep e2 e2' ->
              epstep (EApp e1 e2) (EApp e1 e2')
  | PsLamT : #t:typ ->
             #t':typ ->
             ebody:exp ->
             =ht:tstep t t' ->
             epstep (ELam t ebody) (ELam t' ebody)
  | PsIf0E0 : #e0:exp ->
              #e0':exp ->
              ethen:exp ->
              eelse:exp ->
              =ht:epstep e0 e0' ->
              epstep (EIf0 e0 ethen eelse) (EIf0 e0' ethen eelse)

type cfg =
  | Cfg : h:heap -> e:exp -> cfg

type eistep : cfg -> cfg -> Type =
  | IsRd :  h:heap ->
            l:loc ->
            eistep (Cfg h (ebang (eloc l))) (Cfg h (eint (h l)))
  | IsWr :  h:heap ->
            l:loc ->
            i:int ->
            eistep (Cfg h (eassign (eloc l) (eint i)))
                   (Cfg (upd_heap l i h) eunit)
  | IsBeta :  h:heap ->
              t:typ ->
              ebody:exp ->
              v:value ->
              eistep (Cfg h (EApp (ELam t ebody) v))
                     (Cfg h (esubst_ebeta v ebody))
  | IsIf0 :  h:heap ->
             e1:exp ->
             e2:exp ->
             eistep (Cfg h (EIf0 (eint 0) e1 e2)) (Cfg h e1)
  | IsIfS :  h:heap ->
             i:int{i<>0} ->
             e1:exp ->
             e2:exp ->
             eistep (Cfg h (EIf0 (eint i) e1 e2)) (Cfg h e2)
  | IsAppE1 : h:heap ->
              #e1:exp ->
              #e1':exp ->
              e2:exp ->
              =ht:epstep e1 e1' ->
              eistep (Cfg h (EApp e1 e2)) (Cfg h (EApp e1' e2))
  | IsAppE2 : h:heap ->
              e1:exp ->
              #e2:exp ->
              #e2':exp ->
              =ht:epstep e2 e2' ->
              eistep (Cfg h (EApp e1 e2)) (Cfg h (EApp e1 e2'))
  | IsIf0E0 : h:heap ->
              #e0:exp ->
              #e0':exp ->
              ethen:exp ->
              eelse:exp ->
              =ht:epstep e0 e0' ->
              eistep (Cfg h (EIf0 e0 ethen eelse))
                     (Cfg h (EIf0 e0' ethen eelse))

(********************************************************)
(* The signatures of Pure and ST and other Monad ops    *)
(********************************************************)
let k_pre_pure    = KType
let k_pre_all     = KTArr theap KType

let k_post_pure t = KTArr t KType
let k_post_all  t = KTArr t (KTArr theap KType)

let k_pure t      = KKArr (k_post_pure t) k_pre_pure
let k_all  t      = KKArr (k_post_all  t) k_pre_all

let k_m m = match m with
| EfPure -> k_pure
| EfAll  -> k_all

let tot t = Cmp EfPure t (TTLam (k_post_pure t)
                           (tforalle (ttsh t) (TEApp (TVar 1) (EVar 0))))

val return_pure : t:typ -> e:exp -> Tot typ
let return_pure t e = TTLam (k_post_pure t) (TEApp (TVar 0) e)

val return_all : t:typ -> e:exp -> Tot typ
let return_all t e = TTLam (k_post_all t) (TELam theap
                    (TEApp (TEApp (TVar 0) (eesh (etsh e))) (EVar 0)))

(*TODO: do not forget to shift up e !!!*)
(*Actually, can it have free variables ?*)
val bind_pure:  ta : typ -> tb : typ
             -> wp : typ
             -> f  : typ
             -> Tot typ
let bind_pure ta tb wp f =
   TTLam (k_post_pure tb) (*p*)
     (TTApp (ttsh wp)
        (TELam (*shift*)(ttsh tb)(*x*)
           (TTApp (TEApp (ttsh (tesh f)) (EVar 0)) (TVar 0))))

val bind_all:  ta:typ -> tb:typ
             ->wp : typ
             ->f  : typ
             ->Tot typ
let bind_all ta tb wp f =
  (TTLam (k_post_all tb) (*p*)
     (TTApp (ttsh wp)
        (TELam (ttsh tb) (*x*)
           (TELam theap
              (TEApp (TTApp (TEApp (ttsh (tesh (tesh f))) (EVar 1))
                            (TVar 0))
                     (EVar 0))))))

val monotonic_pure : a:typ -> wp:typ -> Tot typ
let monotonic_pure a wp =
  tforallt (k_post_pure a)
    (tforallt (k_post_pure (ttsh a))
        (timpl
          ((*forall x. p1 x ==> p2 x *)
            tforalle (ttsh (ttsh a))
               (timpl  (TEApp (TVar 1 (*p1*)) (EVar 0))
                       (TEApp (TVar 0 (*p2*)) (EVar 0))
               )
          )
          ((*wp p1 ==> wp p2*)
            timpl (TTApp (ttsh (ttsh wp)) (TVar 1))
                  (TTApp (ttsh (ttsh wp)) (TVar 0))
          )
        )
     )

val monotonic_all : a:typ -> wp:typ -> Tot typ
let monotonic_all a wp =
  tforallt (k_post_pure a)
    (tforallt (k_post_pure (ttsh a))
        (
          timpl
          ((*forall x. p1 x ==> p2 x *)
            tforalle (ttsh (ttsh a))
               (tforalle theap
                    (timpl  (TEApp (TEApp (TVar 1 (*p1*)) (EVar 1(*x*))) (EVar 0) )
                            (TEApp (TEApp (TVar 0 (*p2*)) (EVar 1)) (EVar 0))
                    )
               )
          )
          ((*wp p1 ==> wp p2*)
            tforalle theap
              (timpl (TEApp (TTApp (ttsh (ttsh wp)) (TVar 1)) (EVar 0))
                     (TEApp (TTApp (ttsh (ttsh wp)) (TVar 0)) (EVar 0))
              )
          )
        )
    )

let monotonic m = match m with
  | EfPure -> monotonic_pure
  | EfAll  -> monotonic_all

val op_pure : a:typ -> op:(typ -> typ -> Tot typ) ->
              wp1:typ -> wp2:typ -> Tot typ
let op_pure a op wp1 wp2 =
  TTLam (k_post_pure a) (op (TTApp (ttsh wp1) (TVar 0))
                            (TTApp (ttsh wp2) (TVar 0)))

val op_all : a:typ -> op:(typ -> typ -> Tot typ) ->
             wp1:typ -> wp2:typ -> Tot typ
let op_all a op wp1 wp2 =
  TTLam (k_post_all a)
    (TELam theap (op (TEApp (TTApp (tesh (ttsh wp1)) (TVar 0)) (EVar 0))
                     (TEApp (TTApp (tesh (ttsh wp2)) (TVar 0)) (EVar 0))))

let op m =
  match m with
  | EfPure -> op_pure
  | EfAll  -> op_all

val up_pure : a:typ -> t:typ -> Tot typ
let up_pure a t =
  TTLam (k_post_pure a) (ttsh t)

val up_all : a:typ -> t:typ -> Tot typ
let up_all a t =
  TTLam (k_post_pure a) (TELam theap (tesh (ttsh t)))

let up m =
  match m with
  | EfPure -> up_pure
  | EfAll  -> up_all

val down_pure : a:typ -> wp:typ -> Tot typ
let down_pure a wp =
  tforallt (k_post_pure a) (TTApp (ttsh wp) (TVar 0))

val down_all : a : typ -> wp:typ -> Tot typ
let down_all a wp =
  tforallt (k_post_all a)
     (tforalle theap
         (TEApp (TTApp (tesh (ttsh wp)) (TVar 0)) (EVar 0)))

let down m =
  match m with
  | EfPure -> down_pure
  | EfAll  -> down_all

val closee_pure : a:typ -> b:typ -> f:typ -> Tot typ
let closee_pure a b f =
  TTLam (k_post_pure a) (*p*)
  (tforalle (ttsh b)
    (TTApp (TEApp (tesh (ttsh f)) (EVar 0)) (TVar 0)))

val closee_all : a:typ -> b:typ -> f:typ -> Tot typ
let closee_all a b f =
  TTLam (k_post_all a) (*p*)
  (TELam theap (
    (tforalle (tesh (ttsh b))
      (TEApp (TTApp (TEApp (tesh (tesh (ttsh f))) (EVar 0)) (TVar 0))
             (EVar 1)))))

val closet_pure : a:typ -> f:typ -> Tot typ
let closet_pure a f =
  TTLam (k_post_pure a)
  (tforallt KType
    (TTApp (TTApp (ttsh (ttsh f)) (TVar 0)) (TVar 1)))

val closet_all : a:typ -> f:typ -> Tot typ
let closet_all a f =
  TTLam (k_post_all a)
  (TELam theap
    (tforallt KType
      (TEApp (TTApp (TTApp (ttsh (tesh (ttsh f))) (TVar 0)) (TVar 1)) (EVar 0))))

val ite_pure : a:typ -> wp0:typ -> wp1:typ -> wp2:typ -> Tot typ
let ite_pure a wp0 wp1 wp2 =
  bind_pure tint a wp0
  (
   TELam (tint)
    (
      op_pure (tesh a) tand
      ((*up (i=0) ==> wp1*)
       op_pure (tesh a) timpl
        (
         up_pure (tesh a)
           (teqe (EVar 0) (eint 0))
        )
         wp1
      )
      ((*up (i!=0) ==> wp2*)
       op_pure (tesh a) timpl
        (
         up_pure (tesh a)
           (tnot (teqe (EVar 0) (eint 0)))
        )
         wp2
      )
    )
  )

val ite_all : a:typ -> wp0:typ -> wp1:typ -> wp2:typ -> Tot typ
let ite_all a wp0 wp1 wp2 =
  bind_all tint a wp0
  (
   TELam (tint)
    (
      op_all (tesh a) tand
      ((*up (i=0) ==> wp1*)
       op_all (tesh a) timpl
        (
         up_all (tesh a)
           (teqe (EVar 0) (eint 0))
        )
         wp1
      )
      ((*up (i!=0) ==> wp2*)
       op_all (tesh a) timpl
        (
         up_all (tesh a)
           (tnot (teqe (EVar 0) (eint 0)))
        )
         wp2
      )
    )
  )

val ite : m:eff -> a:typ -> wp0:typ -> wp1:typ -> wp2:typ -> Tot typ
let ite m =
  match m with
  | EfPure -> ite_pure
  | EfAll  -> ite_all

val valid_pure : typ -> Tot typ
let valid_pure p = p

val valid_all : typ -> Tot typ
let valid_all p =
  tforalle (theap) (TEApp (tesh p) (EVar 0))

val lift_pure_all : a:typ -> wp:typ -> Tot typ
let lift_pure_all a wp =
  TTLam (k_post_all a)
  (
   TELam theap
   (
    TTApp (tesh (ttsh wp))
     (
      TELam (tesh (ttsh a))
       (
        TEApp (TEApp (TVar 0) (EVar 0)) (EVar 1)
       )
     )
   )
  )

val eff_sub : m1:eff -> m2:eff -> Tot bool
let eff_sub m1 m2 =
  match m1,m2 with
  | EfPure,EfPure -> true
  | EfPure,EfAll  -> true
  | EfAll,EfAll   -> true
  | EfAll,EfPure  -> false

val lift : m1:eff -> m2:eff{eff_sub m1 m2} -> a:typ -> wp:typ -> Tot typ
let lift m1 m2 =
  match m1, m2 with
  | EfPure, EfAll  -> lift_pure_all
  | EfPure, EfPure -> (fun a wp -> wp)
  | EfAll, EfAll -> (fun a wp -> wp)

val bind : m:eff -> ta:typ -> tb:typ -> wp:typ -> f:typ -> Tot typ
let bind m ta tb wp f =
  match m with
  | EfPure -> bind_pure ta tb wp f
  | EfAll  -> bind_all ta tb wp f

val tfix_wp : tx:typ -> t'':typ -> d:exp -> wp:typ -> Tot typ
let tfix_wp tx t'' d wp =
  op_pure t'' tand
          (up_pure (t'') (TEApp (TEApp (TConst TcPrecedes) (EApp d (EVar 0)))
                                (EApp d (EVar 1)))) wp

val sub_computation : phi:typ -> m:eff -> t:typ -> wp : typ -> m':eff{eff_sub m' m} -> t':typ -> w':typ -> Tot typ
let sub_computation phi m t wp m' t' wp' =
tand phi (down m t (op m t timpl wp (lift m' m t' wp')))

(********************************************************)
(* Signature for type and expression constants          *)
(********************************************************)

val tconsts : tconst -> Tot knd
let tconsts tc =
  match tc with
  | TcUnit
  | TcInt
  | TcRefInt
  | TcHeap
  | TcFalse     -> KType

  | TcAnd       -> KKArr KType (KKArr KType KType)

  | TcForallE   -> KKArr KType (KKArr (KTArr (TVar 0) KType) KType)

  | TcEqE       -> KKArr KType (KTArr (TVar 0) (KTArr (TVar 0) KType))

  | TcPrecedes  -> KKArr KType (KKArr KType
                                      (KTArr (TVar 0) (KTArr (TVar 1) KType)))

  | TcEqT     k -> KKArr k (KKArr (ktsh k) KType)

  | TcForallT k -> KKArr (KKArr k KType) KType

let cmp_bang x =
  Cmp EfAll tint (TTLam (k_post_all tint) (TELam theap
                   (TEApp (TEApp (TVar 1) (esel (EVar 0) x)) (EVar 0))))

let cmp_assign x y =
  Cmp EfAll tunit (TTLam (k_post_all tunit) (TELam theap
                    (TEApp (TEApp (TVar 1) eunit) (eupd (EVar 0) x y))))
val teshg : n:nat (*eshift*) -> t:typ -> Tot typ
let rec teshg n t = 
if n = 0 then t 
else tesh (teshg (n-1) t)
  (*
        fix_pure : tx:Type -> t':(tx->Type) -> t'':(tx->Type) ->
                   wp:(x:tx->K_PURE(t'' x)) -> d:(x:tx -> Tot (t' x)) ->
                   F:(x:tx -> f: (y:tx -> PURE (t'' y)
                                 (up_PURE (precedes (d y) (d x)) /\_PURE (wp y)))
                           -> PURE (t'' x) (wp x)) ->
                   Tot t  (where t = y:tx -> PURE (t'' y) (wp y))

       fix_omega : tx:Type -> t':(tx->Type) -> wp:(x:tx->K_ALL(t' x)) ->
                   F:(x:tx -> f:t -> ALL (t' x) (wp x)) -> Tot t
                               (where t = y:tx -> ALL (t' y) (wp y))
			       *)
let tfixpured tx t' = TArr (tx) (tot (TEApp (tesh t') (EVar 0)))
let tfixpuref tx t'' wp = TArr (teshg 2 tx) (Cmp EfPure (TEApp (teshg 3 t'') (EVar 0)) (op_pure (TEApp (teshg 3 t'') (EVar 0)) tand (up_pure (TEApp (teshg 3 t'') (EVar 0)) (tprecedes (EApp (EVar 2) (EVar 0)) (EApp (EVar 2) (EVar 1)))) (TEApp (teshg 3 wp) (EVar 0))))
let tfixpureF tx t'' wp = TArr (tesh tx) (tot (TArr (tfixpuref tx t'' wp) (Cmp EfPure (teshg 3 t'') (TEApp (teshg 3 wp) (EVar 1)))))
let tfixpuret tx t'' wp = TArr (teshg 2 tx) (Cmp EfPure (TEApp (teshg 3 t'') (EVar 0)) (TEApp (teshg 3 wp) (EVar 0)))
let tfixpure tx t' t'' wp = TArr (tfixpured tx t') (tot (TArr (tfixpureF tx t'' wp) (tot (tfixpuret tx t'' wp))))

let tfixomegat tx t' wp = TArr (tesh tx) (Cmp EfAll (TEApp (teshg 2 t') (EVar 0)) (TEApp (teshg 2 wp) (EVar 0))) 
let tfixomegaF tx t' wp = TArr (tx) (tot (TArr (tfixomegat tx t' wp) (Cmp EfAll (TEApp (teshg 2 t') (EVar 1)) (TEApp (teshg 2 wp) (EVar 1)))))
let tfixomega tx t' wp = TArr (tfixomegaF tx t' wp) (tot (tfixomegat tx t' wp))
val econsts : econst -> Tot typ
let econsts ec =
  match ec with
  | EcUnit   -> tunit
  | EcInt _  -> tint
  | EcLoc _  -> tref
  | EcBang   -> TArr tref (cmp_bang (EVar 0))
  | EcAssign -> TArr tref (tot (TArr tint (cmp_assign (EVar 1) (EVar 0))))
  | EcSel    -> TArr theap (tot (TArr tref (tot tint)))
  | EcUpd    -> TArr theap (tot (TArr tref (tot (TArr tint (tot theap)))))
  | EcHeap _ -> theap
  | EcFixPure tx t' t'' wp -> tfixpure tx t' t'' wp
  | EcFixOmega tx t' wp -> tfixomega tx t' wp

(***********************)
(* Head normal forms   *)
(***********************)

(* head_eq (and head_const_eq) might seem too strong,
   but we only use their negation, which should be weak enough
   to be closed under substitution for instance. *)

val head_const : typ -> Tot (option tconst)
let rec head_const t =
  match t with
  | TConst tc  -> Some tc
  | TTApp t1 _
  | TEApp t1 _ -> head_const t1
  | _          -> None

val head_const_eq : ot1:(option tconst) -> ot2:(option tconst) -> Tot bool
let head_const_eq ot1 ot2 =
  match ot1, ot2 with
  | Some (TcForallT _), Some (TcForallT _)
  | Some (TcEqT _)    , Some (TcEqT _)     -> true
  | _                 , _                  -> ot1 = ot2

val is_hnf : typ -> Tot bool
let is_hnf t = is_TArr t || is_Some (head_const t)

val head_eq : t1:typ{is_hnf t1} -> t2:typ{is_hnf t2} -> Tot bool
let head_eq t1 t2 =
  if (is_TArr t1 && is_TArr t2) then
     Cmp.m (TArr.c t1) = Cmp.m (TArr.c t2)
  else
     is_Some (head_const t1) && head_const_eq (head_const t1) (head_const t2)

val econst_eq : ec1 : econst -> ec2 : econst -> Tot bool
let econst_eq ec1 ec2 =
match ec1,ec2 with
| EcFixPure _ _ _ _, EcFixPure _ _ _ _ -> true
| EcFixOmega _ _ _, EcFixOmega _ _ _ -> true
| _ , _ -> ec1 = ec2

(***********************)
(* Precedes on values  *)
(***********************)

val precedes : v1:value -> v2:value -> Tot bool
let precedes v1 v2 =
  match v1, v2 with
  | EConst (EcInt i1), EConst (EcInt i2) -> i1 >= 0 && i2 >= 0 && i1 < i2
  | _, _ -> false

(***********************)
(* Typing environments *)
(***********************)

type eenv = var -> Tot (option typ)
type tenv = var -> Tot (option knd)

val eempty : eenv
let eempty x = None

val tempty : tenv
let tempty x = None

type env =
| Env : e:eenv -> t:tenv -> env

let empty = Env eempty tempty

val enveshift : env -> Tot env
let enveshift e =
  let Env eenvi tenvi = e in
  let eenvi' : eenv = fun (x:var) -> omap tesh (eenvi x) in
  let tenvi' : tenv = fun (x:var) -> omap kesh (tenvi x) in
  Env eenvi' tenvi'

val envtshift : env -> Tot env
let envtshift e =
  let Env eenvi tenvi = e in
  let eenvi' : eenv = fun x -> omap ttsh (eenvi x) in
  let tenvi' : tenv = fun x -> omap ktsh (tenvi x) in
  Env eenvi' tenvi'

(* SF: Let's assume we just need to extend at 0 *)
(* SF: with this version, it was not possible to prove simple things about the env*)
(*
val eextend : typ -> env -> Tot env
let eextend t e =
  let Env eenvi tenvi = e in
  let eenvi' : eenv = fun x -> if x = 0 then Some t
                               else eenvi (x-1)
  in enveshift (Env eenvi' tenvi)
*)
val eextend : typ -> env -> Tot env
let eextend t e =
  let Env eenvi tenvi = e in
  let eenvi' : eenv = fun x -> if x = 0 then Some (tesh t)
                                        else omap tesh (eenvi (x-1))
  in
  let tenvi' : tenv = fun x -> omap kesh (tenvi x) in
  Env eenvi' tenvi'


(*
val textend : knd -> env -> Tot env
let textend k e =
  let Env eenvi tenvi = e in
  let tenvi' : tenv = fun x -> if x = 0 then Some k
                               else tenvi (x-1)
  in envtshift (Env eenvi tenvi')
*)
val textend : knd -> env -> Tot env
let textend k e =
  let Env eenvi tenvi = e in
  let eenvi' : eenv = fun x -> omap ttsh (eenvi x) in
  let tenvi' : tenv = fun x -> if x = 0 then Some (ktsh k)
                               else omap ktsh (tenvi (x-1))
  in (Env eenvi' tenvi')

val lookup_evar : env -> var -> Tot (option typ)
let lookup_evar g x = Env.e g x

val lookup_tvar : env -> var -> Tot (option knd)
let lookup_tvar g x = Env.t g x

(**************************)
(* Environment properties *)
(**************************)

val ext_of_eextend1 : g1:env -> t1:typ -> g2:env -> t2:typ -> Lemma (requires (eextend t1 g1 = eextend t2 g2)) (ensures (t1 = t2))
let ext_of_eextend1 g1 t1 g2 t2 =
let t1' = tsubst sub_edec (Some.v (lookup_evar (eextend t1 g1) 0)) in
let t2' = tsubst sub_edec (Some.v (lookup_evar (eextend t2 g2) 0)) in
tsubst_comp sub_edec sub_einc t1;
tsubst_comp sub_edec sub_einc t2;
edec_einc_comp ();
tsubst_with_sub_id t1;
tsubst_with_sub_id t2

val ext_of_eextend2 : g1:env -> t1:typ -> g2:env -> t2:typ{eextend t1 g1 = eextend t2 g2} -> x:var -> Lemma (Env.e g1 x = Env.e g2 x)
let ext_of_eextend2 g1 t1 g2 t2 x =
match Env.e (eextend t1 g1) (x+1) with
| None -> ()
| Some t ->
(let t' = tsubst sub_edec t in
let t1' = Some.v (Env.e g1 x) in
let t2' = Some.v (Env.e g2 x) in
tsubst_comp sub_edec sub_einc t1';
tsubst_comp sub_edec sub_einc t2';
edec_einc_comp();
tsubst_with_sub_id t1';
tsubst_with_sub_id t2')

val ext_of_eextend2' : g1:env -> t1:typ -> g2:env -> t2:typ{eextend t1 g1 = eextend t2 g2} -> Lemma (Env.e g1 = Env.e g2 )
let ext_of_eextend2' g1 t1 g2 t2  =
forall_intro (ext_of_eextend2 g1 t1 g2 t2);
cut (FEq (Env.e g1) (Env.e g2))

val ext_of_eextend3 : g1:env -> t1:typ -> g2:env -> t2:typ{eextend t1 g1 = eextend t2 g2}-> a:var ->  Lemma (Env.t g1 a = Env.t g2 a)
let ext_of_eextend3 g1 t1 g2 t2 a =
match Env.t (eextend t1 g1) a with
| None -> ()
| Some k ->
(let k' = ksubst sub_edec k in
let k1' = Some.v (Env.t g1 a) in
let k2' = Some.v (Env.t g2 a) in
ksubst_comp sub_edec sub_einc k1';
ksubst_comp sub_edec sub_einc k2';
edec_einc_comp();
ksubst_with_sub_id k1';
ksubst_with_sub_id k2')

val ext_of_eextend3' : g1:env -> t1:typ -> g2:env -> t2:typ{eextend t1 g1 = eextend t2 g2} -> Lemma (Env.t g1 = Env.t g2 )
let ext_of_eextend3' g1 t1 g2 t2 =
forall_intro(ext_of_eextend3 g1 t1 g2 t2);
cut(FEq (Env.t g1) (Env.t g2))

val ext_of_eextend : g1:env -> t1:typ -> g2:env -> t2:typ{eextend t1 g1 = eextend t2 g2} -> Lemma (g1 = g2 /\ t1 = t2)
let ext_of_eextend g1 t1 g2 t2 =
ext_of_eextend1 g1 t1 g2 t2;
ext_of_eextend2' g1 t1 g2 t2;
ext_of_eextend3' g1 t1 g2 t2

val ext_of_textend : g1:env -> k1:knd -> g2:env -> k2:knd{textend k1 g1 = textend k2 g2} -> Lemma (g1 = g2 /\ k1 = k2)
let ext_of_textend g1 k1 g2 k2 =
(*SF : the same than above ^ *)
admit()

val build_gbase : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> Tot env
let build_gbase g t g' k' =
let eenvibase : eenv = fun x -> omap ttshd (Env.e g x) in
let tenvibase : tenv = fun a -> omap ktshd (Env.t g' a) in
Env eenvibase tenvibase

val get_pullback1 : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> x:var -> Lemma (Env.e (textend k' (eextend (ttshd t) (build_gbase g t g' k'))) x =  Env.e (textend k' g') x)
let get_pullback1 g t g' k' x =
admit()
(*SF : this proof is slow*)
(*
match x with
| 0 -> (
let t'' = Some.v (Env.e (textend k' (eextend (ttshd t) (build_gbase g t g' k'))) x) in
(* ttsh (tesh (ttshd t)) *)
assert (t'' = ttsh (tesh (ttshd t)));
tesh_ttshd t;
(* ttsh (ttshd (tesh t)) (= ttsh (ttshd ( (eextend t g) 0)))*)
let t' = Some.v (Env.e (eextend t g) 0) in
let tp = Some.v (Env.e g' 0) in
assert (t' = tesh t);
assert (t' = ttsh tp);
(* ttsh (ttshd (ttsh tp)) *)
ttshd_ttsh tp
(* ttsh tp = textend k' g' 0*)
)
| n ->
(
match (Env.e (textend k' (eextend (ttshd t) (build_gbase g t g' k'))) x) with
| None -> ()
| Some t'' ->
(
let tg = Some.v (Env.e g (x-1)) in
(*ttsh (tesh (ttshd tg))*)
assert(t'' = ttsh (tesh (ttshd tg)));
tesh_ttshd tg;
(*ttsh (ttshd (tesh tg))*)
let tg' = Some.v (Env.e (eextend t g) x) in
let tp = Some.v (Env.e g' x) in
assert(tg' = tesh tg);
(*ttsh (ttshd (ttsh (g' x)))*)
ttshd_ttsh tp
)
)
*)
val get_pullback1' : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> Lemma (Env.e (textend k' (eextend (ttshd t) (build_gbase g t g' k'))) =  Env.e (textend k' g'))
let get_pullback1' g t g' k' =
forall_intro (get_pullback1 g t g' k');
cut(FEq (Env.e (textend k' (eextend (ttshd t) (build_gbase g t g' k')))) (Env.e (textend k' g')))

val get_pullback2 : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> x:var -> Lemma (Env.t (textend k' (eextend (ttshd t) (build_gbase g t g' k'))) x =  Env.t (textend k' g') x)
let get_pullback2 g t g' k' x = admit() (*Same as above*)

val get_pullback2' : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> Lemma (Env.t (textend k' (eextend (ttshd t) (build_gbase g t g' k'))) =  Env.t (textend k' g'))
let get_pullback2' g t g' k' =
forall_intro (get_pullback2 g t g' k');
cut(FEq (Env.t (textend k' (eextend (ttshd t) (build_gbase g t g' k')))) (Env.t (textend k' g')))

val get_pullback3 : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> Lemma (textend k' (eextend (ttshd t) (build_gbase g t g' k')) =  textend k' g')
let get_pullback3 g t g' k' =
get_pullback1' g t g' k';
get_pullback2' g t g' k'

(*
get_pulback{4|5}{ |'}
*)
val get_pullback6 : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> Lemma (eextend t (textend (keshd k') (build_gbase g t g' k')) =  eextend t g)
let get_pullback6 g t g' k' = admit() (*Same as above*)

val get_pullback7 : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> Lemma (ttsh (ttshd t) = t)
let get_pullback7 g t g' k' =
let t' = Some.v (Env.e (eextend t g) 0) in
let tg = Some.v (Env.e g' 0) in
(* t' = tesh t = ttsh (g' 0) *)
let t1 = tesh (ttsh (ttshd t)) in
tesh_ttsh (ttshd t);
(*ttsh (tesh (ttshd t))*)
tesh_ttshd t;
(*ttsh (ttshd (ttsh (g' 0)))*)
ttshd_ttsh tg;
(*tesh t*)
teshd_tesh t;
teshd_tesh (ttsh (ttshd t))

val get_pullback8 : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> Lemma (kesh (keshd k') = k')
let get_pullback8 g t g' k' =
let k = Some.v (Env.t (textend k' g') 0) in
let kg = Some.v (Env.t g 0) in
(* k = ktsh k' = kesh (g 0) *)
let k1 = ktsh (kesh (keshd k')) in
kesh_ktsh (keshd k');
(*kesh (ktsh (keshd k'))*)
keshd_ktsh k';
(*kesh (keshd (kesh (g' 0)))*)
keshd_kesh kg;
(*ktsh k'*)
ktshd_ktsh k';
ktshd_ktsh (kesh (keshd k'))


type pullback : env -> typ -> env -> knd -> Type =
| PullBack : g:env -> t:typ -> g':env -> k':knd{eextend t g = textend k' g'} -> gbase : env -> tbase : typ { eextend tbase gbase = g' /\ ttsh tbase = t} -> kbase : knd {textend kbase gbase = g /\ kesh kbase = k'} -> pullback g t g' k'

val get_pullback : g : env -> t : typ -> g' : env -> k':knd{eextend t g = textend k' g'} -> Tot (pullback g t g' k')
let get_pullback g t g' k' =
  let gbase = build_gbase g t g' k' in
  let tbase = ttshd t in
  let kbase = keshd k' in
  get_pullback3 g t g' k';
  ext_of_textend (eextend tbase gbase) k' g' k';
  assert (eextend tbase gbase = g');
  get_pullback6 g t g' k';
  ext_of_eextend (textend kbase gbase) t g t;
  assert (textend kbase gbase = g);
  get_pullback7 g t g' k';
  get_pullback8 g t g' k';
  PullBack g t g' k' gbase tbase kbase

(*SF: ^ normally useless now. but maybe used later …*)

(**************)
(*   Typing   *)
(**************)

type typing : env -> exp -> cmp -> Type =

| TyVar : #g:env -> x:var{is_Some (lookup_evar g x)} ->
              typing g (EVar x) (tot (Some.v (lookup_evar g x)))

| TyConst : g:env -> c:econst -> ecwf g c ->
              typing g (EConst c) (tot (econsts c))

| TyAbs : #g:env ->
          #t1:typ ->
          #ebody:exp ->
          m:eff ->
          t2:typ ->
          wp:typ ->
          =hk:kinding g t1 KType ->
           typing (eextend t1 g) ebody (Cmp m t2 wp) ->
           typing g (ELam t1 ebody) (tot (TArr t1 (Cmp m t2 wp)))
(*
    G |- t : Type
    G |- d : Tot (x:tx -> Tot t')
    t = y:tx -> PURE t'' wp
    G, x:tx, f: (y:tx -> PURE t'' (up_PURE (d y << d x) /\_PURE wp))
       |- e : (PURE t'' wp[x/y])
    ---------------------------------------------------------------- [T-Fix]
    G |- let rec (f^d:t) x = e : Tot t


    G |- t : Type
    t = y:tx -> ALL t' wp
    G, x:tx, f:t |- e : (ALL t' wp[x/y])
    ------------------------------------ [T-FixOmega]
    G |- let rec (f:t) x = e : Tot t
*)

| TyIf0 : g:env -> e0 : exp -> e1:exp -> e2:exp -> m:eff ->
          t:typ -> wp0 : typ -> wp1 : typ -> wp2:typ ->
          typing g e0 (Cmp m tint wp0) ->
          typing g e1 (Cmp m t wp1) ->
          typing g e2 (Cmp m t wp2) ->
          typing g (EIf0 e0 e1 e2) (Cmp m t (ite m t wp0 wp1 wp2))
(* SF: I can not prove the TyIf0 case in typing_substitution if I # too many parameters *)

| TyApp : #g:env -> #e1:exp -> #e2:exp -> #m:eff -> #t:typ ->
          #t':typ -> #wp : typ -> #wp1:typ -> #wp2:typ  ->
          typing g e1 (Cmp m (TArr t (Cmp m t' wp)) wp1) ->
          typing g e2 (Cmp m t wp2) ->
          kinding g (tsubst_ebeta e2 t') KType ->
          (* CH: Let's completely ignore this for now,
                 it's strange and I'm not sure it's really needed.
          htot:option (typing g e2 (tot t)){teappears_in 0 t' ==> is_Some htot} -> *)
          typing g (EApp e1 e2) (Cmp m (tsubst_ebeta e2 t')
                                     (bind m (TArr t (Cmp m t' wp)) t wp1 wp2))

| TyRet : #g:env -> #e:exp -> t:typ ->
          typing g e (tot t) ->
          typing g e (Cmp EfPure t (return_pure t e))

| TySub : #g:env -> #e:exp -> #c':cmp -> #c:cmp -> #phi:typ ->
          =ht:typing g e c' ->
          =hsc:scmp g c' c phi ->
          =hv:validity g phi ->
              typing g e c

and scmp : g:env -> c1:cmp -> c2:cmp -> phi:typ -> Type =

| SCmp : #g:env -> m':eff -> #t':typ -> wp':typ ->
          m:eff{eff_sub m' m} -> #t:typ -> wp:typ -> #phi:typ ->
         =hs:styping g t' t phi ->
         =hk:kinding g wp (k_m m t) ->
         =hv:validity g (monotonic m t wp) ->
             scmp g (Cmp m' t' wp') (Cmp m t wp)
               (sub_computation phi m t wp m' t' wp')


and styping : g:env -> t':typ -> t:typ -> phi : typ -> Type =
(*SF: a term styping does not tell us that t' is kind KType,
 but it should be ok since we can get that where it is used in TySub*)
| SubConv : #g:env -> #t:typ -> t':typ ->
            =hv:validity g (teqtype t' t) ->
            =hk:kinding g t KType ->
                styping g t' t ttrue

| SubFun : #g:env -> #t:typ -> #t':typ -> #phi:typ ->
           #c':cmp -> #c:cmp -> #psi:typ ->
           =hst:styping g t t' phi ->
	   =hk:kinding g t KType ->
           =hsc:scmp (eextend t g) c' c psi ->
                styping g (TArr t' c') (TArr t c)
                          (tand phi (tforalle t psi))

| SubTrans : #g:env -> #t1:typ -> #t2:typ -> #t3:typ ->
             #phi12:typ -> #phi23:typ ->
             =hs12:styping g t1 t2 phi12 ->
             =hs23:styping g t2 t3 phi23 ->
                   styping g t1 t3 (tand phi12 phi23)
and tcwf : g:env -> tc:tconst -> Type =
| WFTcForallT : #g:env -> #k:knd ->
                kwf g k ->
		tcwf g (TcForallT k)
| WFTcEqT     : #g:env -> #k:knd ->
                kwf g k ->
		tcwf g (TcEqT k)
| WFTcOther    : g:env -> tc:tconst{not(is_TcForallT tc) && not(is_TcEqT tc)} ->
                tcwf g tc
and ecwf : g:env -> ec:econst -> Type =
| WFEcFixPure : #g:env -> #tx : typ -> #t':typ -> #t'':typ -> #wp:typ ->
              kinding g tx KType ->
	      kinding g t' (KTArr tx KType) ->
	      kinding g t'' (KTArr tx KType) ->
	      kinding g wp (KTArr tx (k_pure (TEApp (tesh t'') (EVar 0)))) ->
	      ecwf g (EcFixPure tx t' t'' wp)
| WFEcFixOmega : #g:env -> #tx:typ -> #t':typ  -> #wp:typ ->
                 kinding g tx KType ->
		 kinding g t' (KTArr tx KType) ->
		 kinding g wp (KTArr tx (k_all (TEApp (tesh t') (EVar 0)))) -> 
		 ecwf g (EcFixOmega tx t' wp)
| WFEcOther : g:env -> ec:econst{not(is_EcFixPure ec) && not(is_EcFixOmega ec)} ->
              ecwf g ec
and kinding : g:env -> t : typ -> k:knd -> Type =

| KVar : #g:env -> x:var{is_Some (lookup_tvar g x)} ->
            kinding g (TVar x) (Some.v (lookup_tvar g x))

| KConst : #g:env -> #c:tconst ->
              tcwf g c ->
              kinding g (TConst c) (tconsts c)
(*SF : we do not check the kwf of the parameter of c, is it a problem ?*)

| KArr : #g:env -> #t1:typ -> #t2:typ -> #phi:typ -> #m:eff ->
         =hk1:kinding g t1 KType ->
         =hk2:kinding (eextend t1 g) t2 KType ->
         =hkp:kinding (eextend t1 g) phi (k_m m t2) ->
         =hv :validity (eextend t1 g) (monotonic m t2 phi) ->
              kinding g (TArr t1 (Cmp m t2 phi)) KType

| KTLam : #g:env -> #k:knd -> #t:typ -> #k':knd ->
          =hw:kwf g k ->
          =hk:kinding (textend k g) t k' ->
              kinding g (TTLam k t) (KKArr k k')

| KELam : #g:env -> #t1:typ -> #t2:typ -> #k2:knd ->
          =hk1:kinding g t1 KType ->
          =hk2:kinding (eextend t1 g) t2 k2 ->
               kinding g (TELam t1 t2) (KTArr t1 k2)

| KTApp : #g:env -> #t1:typ -> #t2:typ -> #k:knd -> k':knd ->
          =hk1:kinding g t1 (KKArr k k') ->
          =hk2:kinding g t2 k ->
          =hw :kwf g (ksubst_tbeta t2 k') ->
               kinding g (TTApp t1 t2) (ksubst_tbeta t2 k')

| KEApp : #g:env -> #t:typ -> #t':typ -> #k:knd -> #e:exp ->
          =hk:kinding g t (KTArr t' k) ->
          =ht:typing g e (tot t') ->
          =hw:kwf g (ksubst_ebeta e k) ->
              kinding g (TEApp t e) (ksubst_ebeta e k)

| KSub  : #g:env -> #t:typ -> #k':knd -> #k:knd -> #phi:typ ->
          =hk:kinding g t k' ->
          =hs:skinding g k' k phi ->
          =hv:validity g phi ->
              kinding g t k

and skinding : g:env -> k1:knd -> k2:knd -> phi:typ -> Type=

| KSubRefl : #g:env -> #k:knd ->
             =hw:kwf g k ->
                 skinding g k k ttrue

| KSubKArr : #g:env -> #k1:knd -> #k2:knd -> k1':knd -> k2':knd ->
             #phi1:typ -> #phi2:typ->
             =hs21 :skinding g k2 k1 phi1 ->
	     =hkw:kwf g k2 ->
             =hs12':skinding (textend k2 g) k1' k2' phi2 ->
                    skinding g (KKArr k1 k1') (KKArr k2 k2')
                               (tand phi1 (tforallt k2 phi2))

| KSubTArr : #g:env -> #t1:typ -> #t2:typ -> #k1:knd -> #k2:knd ->
             #phi1:typ -> #phi2:typ ->
             =hs21:styping g t2 t1 phi1 ->
	     =hk:kinding g t2 KType ->
             =hs12':skinding (eextend t2 g) k1 k2 phi2 ->
                    skinding g (KTArr t1 k1) (KTArr t2 k2)
                               (tand phi1 (tforalle t2 phi2))

and kwf : env -> knd -> Type =

| WfType : g:env ->
             kwf g KType

| WfTArr : #g:env -> #t:typ -> #k':knd ->
            =hk:kinding g t KType ->
            =hw:kwf (eextend t g) k' ->
                kwf g (KTArr t k')

| WfKArr : #g:env -> #k:knd -> #k':knd ->
            =hw :kwf g k ->
            =hw':kwf (textend k g) k' ->
                 kwf g (KKArr k k')

and validity : g:env -> t:typ -> Type =

| VAssume : #g:env -> e:exp -> t:typ ->
            =h:typing g e (tot t) ->
               validity g t

| VRedE   : #g:env -> #e:exp -> #t:typ -> #e':exp ->
            =ht :typing g e (tot t) ->
            =ht':typing g e' (tot t) ->
            =hst:epstep e e' ->
                 validity g (teqe e e')

| VEqReflE : #g:env -> #e:exp -> #t:typ ->
             =ht:typing g e (tot t) ->
                 validity g (teqe e e)

| VSubstE  : #g:env -> #e1:exp -> #e2:exp -> #t':typ -> t:typ ->
             =hv12 :validity g (teqe e1 e2) ->
             =ht1  :typing g e1 (tot t') ->
             =ht2  :typing g e2 (tot t') ->
	     (*hkt':kinding g t' KType ->*)
	     (*SF : this one is not compulsory, since
	      we can extract it from typing above*)
             =hk   :kinding (eextend t' g) t KType ->
             =hvsub:validity g (tsubst_ebeta e1 t) ->
                    validity g (tsubst_ebeta e2 t)

| VRedT    : #g:env -> #t:typ -> #t':typ -> #k:knd ->
             =hk :kinding g t k ->
             =hk':kinding g t' k ->
             =hst:tstep t t' ->
                  validity g (teqt k t t')

| VEqReflT : #g:env -> #t:typ -> #k:knd ->
             =hk:kinding g t k ->
                 validity g (teqt k t t)

| VSubstT :  #g:env -> #t1:typ -> #t2:typ -> #k:knd -> t:typ -> 
             =hv12 :validity g (teqt k t1 t2) ->
	     =hkw : kwf g k ->
             =hk   :kinding (textend k g) t KType ->
             =hvsub:validity g (tsubst_tbeta t1 t) ->
                    validity g (tsubst_tbeta t2 t)

| VSelAsHeap : #g:env -> #h:heap -> #l:loc ->
               =hth:typing g (eheap h) (tot theap) ->
               =htl:typing g (eloc l) (tot tref) ->
                    validity g (teqe (esel (eheap h) (eloc l)) (eint (h l)))

| VUpdAsHeap : #g:env -> #h:heap -> #l:loc -> #i:int ->
               =hth:typing g (eheap h) (tot theap) ->
               =htl:typing g (eloc l) (tot tref) ->
               =hti:typing g (eint i) (tot tint) ->
                    validity g (teqe (eupd (eheap h) (eloc l) (eint i))
                                     (eheap (upd_heap l i h)))

| VSelEq : #g:env -> #eh:exp -> #el:exp -> #ei:exp ->
           =hth:typing g eh (tot theap) ->
           =htl:typing g el (tot tref) ->
           =hti:typing g ei (tot tint) ->
                validity g (teqe (esel (eupd eh el ei) el) ei)

| VSelNeq : #g:env -> #eh:exp -> #el:exp -> #el':exp -> #ei:exp ->
            =hth :typing g eh (tot theap) ->
            =htl :typing g el (tot tref) ->
            =htl':typing g el' (tot tref) ->
            =hti :typing g ei (tot tint) ->
            =hv  :validity g (tnot (teqe el el')) ->
                  validity g (teqe (esel (eupd eh el' ei) ei) (esel eh el))

| VForallIntro :  #g:env -> #t:typ -> #phi:typ ->
                 =hk:kinding g t KType ->
                 =hv:validity (eextend t g) phi ->
                     validity g (tforalle t phi)


| VForallTypIntro :  #g:env -> #k:knd -> #phi:typ ->
                    =kw:kwf g k ->
                    =hv:validity (textend k g) phi ->
                        validity g (tforallt k phi)

| VForallElim : #g:env -> #t:typ -> #phi:typ -> #e:exp ->
                =hv:validity g (tforalle t phi) ->
                =ht:typing g e (tot t) ->
                    validity g (tsubst_ebeta e phi)

| VForallTypElim : #g:env -> #t:typ -> #k:knd -> #phi:typ ->
                   =hv:validity g (tforallt k phi) ->
                   =hk:kinding g t k ->
                       validity g (tsubst_tbeta t phi)

| VAndElim1 : #g:env -> #p1:typ -> #p2:typ ->
              =hv:validity g (tand p1 p2) ->
                  validity g p1

| VAndElim2 : #g:env -> #p1:typ -> #p2:typ ->
              =hv:validity g (tand p1 p2) ->
                  validity g p2

| VAndIntro : #g:env -> #p1:typ -> #p2:typ ->
              =hv1:validity g p1 ->
              =hv2:validity g p2 ->
                   validity g (tand p1 p2)

| VExMiddle : #g:env -> #t1:typ -> #t2:typ ->
              =hk1:kinding g t1 KType ->
              =hk2:kinding g t2 KType ->
              =hv1:validity (eextend t1 g) (tesh t2) ->
              =hv2:validity (eextend (tnot t1) g) (tesh t2) ->
              validity g t2

| VOrIntro1 : #g:env -> #t1:typ -> #t2:typ ->
              =hv:validity g t1 ->
              =hk:kinding g t2 KType ->
                  validity g (tor t1 t2)

| VOrIntro2 : #g:env -> #t1:typ -> #t2:typ ->
              =hv:validity g t2 ->
              =hk:kinding g t1 KType ->
                  validity g (tor t1 t2)

| VOrElim : #g:env -> #t1:typ -> #t2:typ -> #t3:typ ->
            =hk1:kinding g t1 KType ->
	    =hk2:kinding g t2 KType ->
            =hk3 :kinding g t3 KType ->
	    =hvor:validity g (tor t1 t2) ->
            =hv1:validity (eextend t1 g) (tesh t3) ->
            =hv2:validity (eextend t2 g) (tesh t3) ->
                 validity g t3

| VFalseElim : #g:env -> #t:typ ->
               =hv:validity g tfalse ->
               =hk:kinding g t KType ->
                   validity g t

| VPreceedsIntro : #g:env -> #v1:value -> #v2:value{precedes v1 v2} ->
                   #t1:typ -> #t2:typ ->
                   =ht1:typing g v1 (tot t1) ->
                   =ht2:typing g v2 (tot t2) ->
                        validity g (tprecedes v1 v2)

| VDistinctC : g:env -> c1:econst -> c2:econst{not (econst_eq c1 c2)} ->
               validity g (tnot (teqe (EConst c1) (EConst c2)))

| VDistinctTH : #g:env -> #t1:typ{is_hnf t1} ->
                          #t2:typ{is_hnf t2 && not (head_eq t1 t2)} ->
                =hk1:kinding g t1 KType ->
                =hk2:kinding g t2 KType ->
                     validity g (tnot (teqtype t1 t2))

(*
For injectivity should probably stick with this (see discussion in txt file):

    G |= x:t1 -> M t2 phi =_Type x:t1' -> M t2' phi'
    -------------------------------------------- [V-InjTH]
    G |= (t1 =_Type t1) /\ (t2 = t2') /\ (phi = phi')
 *)

| VInjTH : #g:env -> #t1 :typ -> #t2 :typ -> #phi :typ ->
                     #t1':typ -> #t2':typ -> #phi':typ -> #m:eff ->
           =hv:validity g (teqtype (TArr t1  (Cmp m t2  phi))
                                   (TArr t1' (Cmp m t2' phi'))) ->
               validity g (tand (tand (teqtype t1 t1') (teqtype (tforalle t1 t2) (tforalle t1 t2')))
                                      (teqtype (tforalle t1 phi) (tforalle t1 phi')))
(* Environment Well-Formedness*)
type ewf : env -> Type =

| GEmpty : ewf empty

| GType  : #g:env -> #t:typ ->
           =hw:ewf g ->
           =hk:kinding g t KType ->
               ewf (eextend t g)

| GKind  : #g:env -> #k:knd ->
           =hw:ewf g ->
           =h:kwf g k ->
              ewf (textend k g)


(**********************)
(* Substitution Lemma *)
(**********************)

(*TODO: prove all those admitted lemmas*)

val subst_on_tot : s:sub -> t:typ -> Lemma (csubst s (tot t) = tot (tsubst s t))
let subst_on_tot s t = admit()

val subst_on_bind : s:sub -> m:eff -> tarr:typ -> t:typ -> wp1 : typ -> wp2 :typ -> Lemma (tsubst s (bind m tarr t wp1 wp2) = bind m (tsubst s tarr) (tsubst s t) (tsubst s wp1) (tsubst s wp2))
let subst_on_bind s m tarr t wp1 wp2 = admit()

val subst_on_return_pure : s:sub -> t:typ -> e:exp -> Lemma (tsubst s (return_pure t e) = return_pure (tsubst s t) (esubst s e))
let subst_on_return_pure s t e = admit()

val subst_on_ite : s:sub -> m : eff -> t:typ -> wp0:typ -> wp1:typ -> wp2:typ ->
Lemma (tsubst s (ite m t wp0 wp1 wp2) = ite m (tsubst s t) (tsubst s wp0) (tsubst s wp1) (tsubst s wp2))
let subst_on_ite m t wp0 wp1 wp2 = admit()

val subst_on_sub_computation : s:sub -> phi:typ -> m:eff -> t:typ -> wp:typ -> m':eff{eff_sub m' m} -> t':typ -> wp':typ -> Lemma (tsubst s (sub_computation phi m t wp m' t' wp') = sub_computation (tsubst s phi) m (tsubst s t) (tsubst s wp) m' (tsubst s t') (tsubst s wp'))
let subst_on_sub_computation s phi m t wp m' t' wp' = admit()

val subst_on_k_m : s:sub -> m:eff -> t:typ -> Lemma (ksubst s (k_m m t) = k_m m (tsubst s t))
let subst_on_k_m s m t = admit()

val subst_on_monotonic : s:sub -> m:eff -> t:typ -> wp:typ -> Lemma (tsubst s (monotonic m t wp) = monotonic m (tsubst s t) (tsubst s wp))
let subst_on_monotonic s m t wp = admit()
val subst_on_teqe : s:sub -> e1:exp -> e2:exp -> Lemma (tsubst s (teqe e1 e2) = teqe (esubst s e1) (esubst s e2))
let subst_on_teqe s e1 e2 = admit()
val subst_on_teqt : s : sub -> k : knd -> t1:typ -> t2:typ -> Lemma (tsubst s (teqt k t1 t2) = teqt (ksubst s k) (tsubst s t1) (tsubst s t2))
let subst_on_teqt s k t1 t2 = admit()

val subst_on_teqtype : s:sub -> t:typ -> t':typ -> Lemma (tsubst s (teqtype t' t) = teqtype (tsubst s t') (tsubst s t))
let subst_on_teqtype s t t' = admit()

val subst_on_esel : s:sub -> eh:exp -> el:exp -> Lemma (esubst s (esel eh el) = esel (esubst s eh) (esubst s el))
let subst_on_esel s eh el = admit()

val subst_on_eupd : s:sub -> eh:exp -> el:exp -> ei:exp -> Lemma (esubst s (eupd (eh) (el) (ei)) = eupd (esubst s eh) (esubst s el) (esubst s ei))
let subst_on_eupd s eh el ei = admit()

val subst_on_teconst : s:sub -> ec:econst -> Lemma (tsubst s (econsts ec) = econsts (ecsubst s ec))
let subst_on_teconst s ec = admit()

val subst_on_tconst : s:sub -> tc:tconst -> Lemma (tconsts (tcsubst s tc) = ksubst s (tconsts tc))
let subst_on_tconst s tc = admit()

val subst_on_tand : s:sub -> a:typ -> b:typ -> Lemma (tsubst s (tand a b) = tand (tsubst s a) (tsubst s b))
let subst_on_tand s a b = admit()

val subst_on_tor : s:sub -> t1 : typ -> t2 : typ -> Lemma (tsubst s (tor t1 t2) = tor (tsubst s t1) (tsubst s t2))
let subst_on_tor s t1 t2 = admit()

val subst_on_tnot : s:sub -> t:typ -> Lemma (tsubst s (tnot t) = tnot (tsubst s t))
let subst_on_tnot s t = admit()

val subst_on_tforallt : s:sub -> k:knd -> body:typ -> Lemma (tsubst s (tforallt k body) = tforallt (ksubst s k) (tsubst (sub_tlam s) body))
let subst_on_tforallt s k body = admit()

val subst_on_tforalle : s:sub -> t:typ -> body:typ -> Lemma (tsubst s (tforalle t body) = tforalle (tsubst s t) (tsubst (sub_elam s) body))
let subst_on_tforalle s t body = admit()

val subst_on_ktarrow : s:sub -> t:typ -> k:knd -> Lemma (ksubst s (KTArr t k) = KTArr (tsubst s t) (ksubst (sub_elam s) k))
let subst_on_ktarrow s t k = () 
val subst_on_tarrow : s:sub -> t1:typ -> m:eff -> t2:typ -> wp:typ ->
Lemma (tsubst s (TArr t1 (Cmp m t2 wp)) = TArr (tsubst s t1) (Cmp m (tsubst (sub_elam s) t2) (tsubst (sub_elam s) wp)))
let subst_on_tarrow s t1 m t2 wp = admit()

val subst_on_elam : s:sub -> t1:typ -> ebody : exp ->
Lemma (esubst s (ELam t1 ebody) = ELam (tsubst s t1) (esubst (sub_elam s) ebody))
let subst_on_elam s t1 ebody = admit()

val tsubst_on_ebeta : s:sub -> e:exp -> t:typ -> Lemma (tsubst s (tsubst_ebeta e t) = tsubst_ebeta (esubst s e) (tsubst (sub_elam s) t))
let tsubst_on_ebeta s e t = admit()
val ksubst_on_ebeta : s:sub -> e:exp -> k:knd -> Lemma (ksubst s (ksubst_ebeta e k) = ksubst_ebeta (esubst s e) (ksubst (sub_elam s) k))
let ksubst_on_ebeta s e k = admit()

val tsubst_on_tbeta : s:sub -> t:typ -> tbody : typ -> Lemma (tsubst s (tsubst_tbeta t tbody) = tsubst_tbeta (tsubst s t) (tsubst (sub_tlam s) tbody))
let tsubst_on_tbeta s t tbody = admit()
val ksubst_on_tbeta : s:sub -> t:typ -> k:knd -> Lemma (ksubst s (ksubst_tbeta t k) = ksubst_tbeta (tsubst s t) (ksubst (sub_tlam s) k))
let ksubst_on_tbeta s t k = admit()

val subst_preserves_tarrow : s:sub -> t:typ -> Lemma (is_TArr t ==> is_TArr (tsubst s t))
let subst_preserves_tarrow s t = ()

val subst_preserves_head_const : s:sub -> t:typ -> Lemma (is_Some (head_const t) ==> is_Some (head_const (tsubst s t)))
let rec subst_preserves_head_const s t =
match t with
| TConst tc -> ()
| TTApp t1 _ -> subst_preserves_head_const s t1
| TEApp t1 _ -> subst_preserves_head_const s t1
| _ -> ()

val subst_on_hnf : s:sub -> t:typ -> Lemma (requires (is_hnf t))
                                           (ensures (is_hnf (tsubst s t) ))
let subst_on_hnf s t = subst_preserves_tarrow s t; subst_preserves_head_const s t

val subst_on_head_const : s:sub -> t:typ -> Lemma (requires (is_Some (head_const t))) (ensures (head_const (tsubst s t) = omap (tcsubst s) (head_const t)))
let rec subst_on_head_const s t =
match t with 
| TConst tc -> ()
| TTApp t1 _ -> subst_on_head_const s t1
| TEApp t1 _ -> subst_on_head_const s t1

val subst_preserves_head_eq : s:sub -> t1:typ{is_hnf t1} -> t2:typ{is_hnf t2} -> Lemma (requires (not (head_eq t1 t2))) (ensures (is_hnf (tsubst s t1) /\ is_hnf (tsubst s t2) /\ not (head_eq (tsubst s t1) (tsubst s t2))))
let subst_preserves_head_eq s t1 t2 = 
(* SF : this proof is working but is slow. Maybe improve it later *)
admit()(*
subst_on_hnf s t1; subst_on_hnf s t2;
if (is_TArr t1 && is_TArr t2) then ()
else if (is_TArr t1 && not (is_TArr t2)) then ()
else if (not (is_TArr t1) && is_TArr t2) then ()
else (subst_on_head_const s t1; subst_on_head_const s t2)
*)

//NS: Writing 'requires' and 'ensures' will  give you better error messages
val tsubst_elam_shift : s:sub -> t:typ -> Lemma (ensures (tsubst (sub_elam s) (tesh t) = tesh (tsubst s t)))
let tsubst_elam_shift s t = admit()

val ksubst_elam_shift : s:sub -> k:knd -> Lemma (ensures (ksubst (sub_elam s) (kesh k) = kesh (ksubst s k)))
let ksubst_elam_shift s k = admit()

val tsubst_tlam_shift : s:sub -> t:typ -> Lemma (tsubst (sub_tlam s) (ttsh t) = ttsh (tsubst s t))
let tsubst_tlam_shift s t = admit()

val ksubst_tlam_shift : s:sub -> k:knd -> Lemma (ksubst (sub_tlam s) (ktsh k) = ktsh (ksubst s k))
let ksubst_tlam_shift s k = admit()

val tyif01 : s:sub -> e0:exp -> e1:exp -> e2:exp -> Lemma (esubst s (EIf0 e0 e1 e2) = EIf0 (esubst s e0) (esubst s e1) (esubst s e2))
let tyif01 s e0 e1 e2 = ()
val tyif02 : s:sub -> m:eff -> wp0:typ -> Lemma(csubst s (Cmp m tint wp0) = Cmp m tint (tsubst s wp0))
let tyif02 s m wp0 = ()
val tyif03 : s:sub -> m:eff -> t:typ -> wp:typ -> Lemma (csubst s (Cmp m t wp) = Cmp m (tsubst s t) (tsubst s wp))
let tyif03 s m t wp = ()

val epstep_substitution : s:sub -> e:exp -> e':exp -> hs:epstep e e' -> Tot (epstep (esubst s e) (esubst s e'))
(decreases %[hs])
val tstep_substitution : s:sub -> t:typ -> t':typ -> hs:tstep t t' -> Tot (tstep (tsubst s t) (tsubst s t'))
(decreases %[hs])
let rec epstep_substitution s e e' hs = match hs with
| PsBeta t ebody v -> admit() (*TODO: code a substitution lemma for values*)
| PsIf0 e1 e2 -> PsIf0 (esubst s e1) (esubst s e2)
| PsIfS i e1 e2 -> PsIfS i (esubst s e1) (esubst s e2)
| PsAppE1 #e1 #e1' e2 ht -> PsAppE1 (esubst s e2) (epstep_substitution s e1 e1' ht)
| PsAppE2 e1 #e2 #e2' ht -> PsAppE2 (esubst s e1) (epstep_substitution s e2 e2' ht)
| PsLamT #t #t' ebody ht -> admit()
| PsIf0E0 #e0 #e0' ethen eelse ht -> admit() (*PsIfE0 (esubst s ethen) (esubst s eelse) (ep*)
| _ -> admit() 
and tstep_substitution s t t' hs = admit()
(**********************)
(* Substitution Arrow *)
(**********************)

type subst_typing : s:sub -> g1:env -> g2:env -> Type =
| SubstTyping : s:sub -> g1:env -> g2:env ->
                ef:(x:var{is_Some (lookup_evar g1 x)} ->
                    Tot(typing g2 (Sub.es s x) (tot (tsubst s (Some.v (lookup_evar g1 x)))))) ->

                tf:(a:var{is_Some (lookup_tvar g1 a)} ->
                    Tot(kinding g2 (Sub.ts s a) (ksubst s (Some.v (lookup_tvar g1 a))))) ->
                subst_typing s g1 g2
| RenamingTyping : s:sub -> g1:env -> g2:env ->
                ef:(x:var{is_Some (lookup_evar g1 x)} ->
                    Tot(hr:typing g2 (Sub.es s x) (tot (tsubst s (Some.v (lookup_evar g1 x)))){is_TyVar hr})) ->

                tf:(a:var{is_Some (lookup_tvar g1 a)} ->
                    Tot(hr:kinding g2 (Sub.ts s a) (ksubst s (Some.v (lookup_tvar g1 a))){is_KVar hr})) ->
                subst_typing s g1 g2
(*I wanted to rewrite the substitution lemma in a 'is_renaming' style (so without the RenamingTyping constructor) but I was not able to make it work*)

val is_renaming_typing : #s:sub -> #g1:env -> #g2:env -> hs:subst_typing s g1 g2 -> Tot (r:nat{is_RenamingTyping hs ==> r = 0 /\ is_SubstTyping hs ==> r = 1})
let is_renaming_typing s g1 g2 hs = if (is_RenamingTyping hs) then 0 else 1

val is_tyvar : #g:env -> #e:exp -> #t:cmp -> ht:typing g e t -> Tot nat
let is_tyvar g e t ht = if is_TyVar ht then 0 else 1

val is_kvar : #g : env -> #t:typ -> #k:knd -> hk : kinding g t k -> Tot nat
let is_kvar g t k hk = if is_KVar hk then 0 else 1

val hs_sub_einc : g:env -> t:typ ->
Tot(r:subst_typing sub_einc g (eextend t g){is_RenamingTyping r})
let hs_sub_einc g t =
      let temp : subst_typing sub_einc g (eextend t g) = RenamingTyping sub_einc g (eextend t g)
		  (fun x ->  TyVar (x+1)
		  )
		  (fun a -> KVar a )
		  in temp
val hs_sub_tinc : g:env -> k:knd -> 
           Tot(r:subst_typing sub_tinc g (textend k g){is_RenamingTyping r})
let hs_sub_tinc g k =
      RenamingTyping sub_tinc g (textend k g)
		  (fun x ->  TyVar x) (fun a -> KVar (a+1))

val hs_sub_id : g:env -> Tot (r:subst_typing sub_id g g{is_RenamingTyping r})
let hs_sub_id g =
RenamingTyping sub_id g g (fun x -> tsubst_with_sub_id (Some.v (lookup_evar g x)); TyVar x) (fun a -> ksubst_with_sub_id (Some.v (lookup_tvar g a)); KVar a)

val compose_with_renaming_arrow : g1 : env -> g2 : env -> g3 : env -> s12 : sub -> s23 : sub -> hs12 : subst_typing s12 g1 g2{ is_RenamingTyping hs12} -> hs23 : subst_typing s23 g2 g3 -> Tot (hr : subst_typing (sub_comp s23 s12) g1 g3)
let compose_with_renaming_arrow g1 g2 g3 s12 s23 hs12 hs23 =
let RenamingTyping _ _ _ ef12 tf12 = hs12 in
match hs23 with
| RenamingTyping _ _ _ ef23 tf23 ->
RenamingTyping (sub_comp s23 s12) g1 g3
(fun x -> let TyVar x' = ef12 x in ef23 x')
(fun a -> let KVar a' = tf12 a in tf23 a')
| SubstTyping _ _ _ ef23 tf23 ->
SubstTyping (sub_comp s23 s12) g1 g3
(fun x -> let TyVar x' = ef12 x in ef23 x')
(fun a -> let KVar a' = tf12 a in tf23 a')


opaque val typing_substitution : #g1:env -> #e:exp -> #c:cmp -> s:sub -> #g2:env ->
    h1:typing g1 e c ->
    hs:subst_typing s g1 g2 ->
    Tot (hr:typing g2 (esubst s e) (csubst s c) {is_RenamingTyping hs /\ is_TyVar h1 ==> is_TyVar hr} )
(decreases %[is_tyvar h1; is_renaming_typing hs; 1;h1])
opaque val scmp_substitution : #g1:env -> #c1:cmp -> #c2:cmp -> #phi:typ -> s:sub -> #g2:env ->
    h1:scmp g1 c1 c2 phi ->
    hs:subst_typing s g1 g2 ->
    Tot (scmp g2 (csubst s c1) (csubst s c2) (tsubst s phi))
(decreases %[1; is_renaming_typing hs; 1; h1])
opaque val styping_substitution : #g1:env -> #t':typ -> #t:typ -> #phi:typ -> s:sub -> #g2:env ->
    h1:styping g1 t' t phi ->
    hs:subst_typing s g1 g2 ->
    Tot (styping g2 (tsubst s t') (tsubst s t) (tsubst s phi))
(decreases %[1;is_renaming_typing hs; 1; h1])
opaque val tcwf_substitution : #g1:env -> #c:tconst -> s:sub -> #g2:env ->
                        h1:tcwf g1 c ->
			hs:subst_typing s g1 g2 ->
			Tot (tcwf g2 (tcsubst s c))
opaque val ecwf_substitution : #g1:env -> #ec:econst -> s:sub -> #g2:env ->
                        h1:ecwf g1 ec ->
			hs:subst_typing s g1 g2 ->
			Tot (ecwf g2 (ecsubst s ec))
(decreases %[1;is_renaming_typing hs; 1; h1])
opaque val kinding_substitution : #g1:env -> #t:typ -> #k:knd -> s:sub -> #g2:env ->
    h1:kinding g1 t k ->
    hs:subst_typing s g1 g2 ->
    Tot (hr:kinding g2 (tsubst s t) (ksubst s k){is_RenamingTyping hs /\ is_KVar h1 ==> is_KVar hr})
(decreases %[is_kvar h1; is_renaming_typing hs; 1; h1])
opaque val skinding_substitution : #g1:env -> #k1:knd -> #k2:knd -> #phi:typ -> s:sub -> #g2:env ->
    h1:skinding g1 k1 k2 phi ->
    hs:subst_typing s g1 g2 ->
    Tot (skinding g2 (ksubst s k1) (ksubst s k2) (tsubst s phi))
(decreases %[1; is_renaming_typing hs; 1; h1])
opaque val kwf_substitution : #g1:env -> #k:knd -> s:sub -> #g2:env ->
    h1:kwf g1 k ->
    hs:subst_typing s g1 g2 ->
    Tot (kwf g2 (ksubst s k))
(decreases %[1;is_renaming_typing hs; 1; h1])
opaque val validity_substitution : #g1:env -> #t:typ -> s:sub -> #g2:env ->
    h1:validity g1 t ->
    hs:subst_typing s g1 g2 ->
    Tot (validity g2 (tsubst s t))
(decreases %[1;is_renaming_typing hs; 1; h1])
opaque val elam_hs : #g1:env -> s:sub -> #g2:env -> t:typ ->
                         hs:subst_typing s g1 g2 ->
                         Tot (hr:subst_typing (sub_elam s) (eextend t g1) (eextend (tsubst s t) g2){is_RenamingTyping hs ==> is_RenamingTyping hr})
(decreases %[1;is_renaming_typing hs; 0; EVar 0])
opaque val tlam_hs : #g1:env -> s:sub -> #g2:env -> k:knd ->
                         hs:subst_typing s g1 g2 ->
                         Tot (hr:subst_typing (sub_tlam s) (textend k g1) (textend (ksubst s k) g2){is_RenamingTyping hs ==> is_RenamingTyping hr})
(decreases %[1;is_renaming_typing hs; 0; TVar 0])
let rec typing_substitution g1 e c s g2 h1 hs =
match h1 with
| TyVar #g1 x ->
admit()(*
( match hs with
| SubstTyping _ _ _ ef tf -> (subst_on_tot s (Cmp.t c); ef x)
| RenamingTyping _ _ _ ef tf -> (subst_on_tot s (Cmp.t c); ef x)
)
*)
| TyConst g ec hw ->
    (
     let hwg2 : ecwf g2 (ecsubst s ec) = ecwf_substitution s hw hs in
     subst_on_tot s (econsts ec);
     subst_on_teconst s ec;
     TyConst g2 (ecsubst s ec) hwg2 )
| TyIf0 g e0 e1 e2 m t wp0 wp1 wp2 he0 he1 he2 ->
admit()(*
    (
      subst_on_ite s m t wp0 wp1 wp2;
      tyif01 s e0 e1 e2;
      tyif02 s m wp0;
      tyif03 s m t wp1;
      tyif03 s m t wp2;
      let he0' : typing g2 (esubst s e0) (Cmp m tint (tsubst s wp0)) = typing_substitution s he0 hs in
      let he1' : typing g2 (esubst s e1) (Cmp m (tsubst s t) (tsubst s wp1)) = typing_substitution s he1 hs in
      let he2' : typing g2 (esubst s e2) (Cmp m (tsubst s t) (tsubst s wp2)) = typing_substitution s he2 hs in
      let h1'  : typing g2 (EIf0 (esubst s e0) (esubst s e1) (esubst s e2)) (Cmp m (tsubst s t) (ite m (tsubst s t) (tsubst s wp0) (tsubst s wp1) (tsubst s wp2))) =
	  TyIf0 g2 (esubst s e0) (esubst s e1) (esubst s e2) m (tsubst s t) (tsubst s wp0) (tsubst s wp1) (tsubst s wp2) he0' he1' he2' in
      h1'
    )
    *)
| TyAbs #g1 #t1 #ebody m t2 wp hk hbody  ->
    (
    let g1ext = eextend t1 g1 in
    let g2ext = eextend (tsubst s t1) g2 in
    let hkt1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk hs in
    let hs'' : subst_typing sub_einc g2 (eextend (tsubst s t1) g2) =
    hs_sub_einc g2 (tsubst s t1) in
    let hs' : subst_typing (sub_elam s) g1ext g2ext=elam_hs s t1 hs in
    let hbodyg2ext : typing g2ext (esubst (sub_elam s) ebody) (Cmp m (tsubst (sub_elam s) t2) (tsubst (sub_elam s) wp)) = typing_substitution (sub_elam s) hbody hs' in
    (*hbodyg2ext -> typing (eextend (tsubst s t1) g2) (esubst (sub_elam s) ebody) (Cmp m (tsubst s t2) (tsubst s wp)) *)
    let elam = ELam (tsubst s t1) (esubst (sub_elam s) ebody) in
    let tarr = TArr t1 (Cmp m t2 wp) in
    let habsg2ext : typing g2 elam (tot (TArr (tsubst s t1) (Cmp m (tsubst (sub_elam s) t2) (tsubst (sub_elam s) wp)))) = TyAbs m (tsubst (sub_elam s) t2) (tsubst (sub_elam s) wp) hkt1g2 hbodyg2ext in
    (*habsg2ext  -> typing g2 (ELam (tsubst s t1) (esubst (sub_elam s) ebody)) (tot (TArr (tsubst s t1) (Cmp m (tsubst (sub_elam s) t2) (tsubst (sub_elam s) wp))))*)
    subst_on_elam s t1 ebody;
    subst_on_tarrow s t1 m t2 wp;
    subst_on_tot s (TArr t1 (Cmp m t2 wp));
    habsg2ext
    )
| TyApp #g #e1 #e2 #m #t #t' #wp #wp1 #wp2 ht1 ht2 hkt' ->
admit()(*
(
let ht1g2 : typing g2 (esubst s e1) (Cmp m (TArr (tsubst s t) (Cmp m (tsubst (sub_elam s) t') (tsubst (sub_elam s) wp))) (tsubst s wp1)) =
subst_on_tarrow s t m t' wp; typing_substitution s ht1 hs in
let ht2g2 : typing g2 (esubst s e2)  (Cmp m (tsubst s t) (tsubst s wp2)) = typing_substitution s ht2 hs in
let hkt'g2 : kinding g2 (tsubst_ebeta (esubst s e2) (tsubst (sub_elam s) t')) KType = tsubst_on_ebeta s e2 t'; kinding_substitution s hkt' hs in
let happg2 : typing g2 (EApp (esubst s e1) (esubst s e2)) (Cmp m (tsubst s (tsubst_ebeta e2 t')) (tsubst s (bind m (TArr t (Cmp m t' wp)) t wp1 wp2))) = tsubst_on_ebeta s e2 t'; subst_on_bind s m (TArr t (Cmp m t' wp)) t wp1 wp2; TyApp ht1g2 ht2g2 hkt'g2 in
happg2
)
*)
| TyRet t ht ->
admit()(*
let htg2 : typing g2 (esubst s e) (tot (tsubst s t))=subst_on_tot s t; typing_substitution s ht hs in
let hretg2 : typing g2 (esubst s e) (Cmp EfPure (tsubst s t) (tsubst s (return_pure t e))) = subst_on_return_pure s t e; TyRet (tsubst s t) htg2 in
hretg2
*)
| TySub #g #e #c' #c #phi ht hsc hv -> 
admit()(*
(
let htg2 : typing g2 (esubst s e) (csubst s c') = typing_substitution s ht hs in
let hscg2 : scmp g2 (csubst s c') (csubst s c) (tsubst s phi) = scmp_substitution s hsc hs in
let hvg2 : validity g2 (tsubst s phi) = validity_substitution s hv hs in
TySub htg2 hscg2 hvg2
)
*)
and scmp_substitution g1 c1 c2 phi s g2 h1 hs =
admit()(*
let SCmp #g m' #t' wp' m #t wp #phi hsub hk hv = h1 in
let hsubg2 = styping_substitution s hsub hs in
let hkg2 : kinding g2 (tsubst s wp) (k_m m (tsubst s t)) = subst_on_k_m s m t; kinding_substitution s hk hs in
let hvg2 : validity g2 (monotonic m (tsubst s t) (tsubst s wp)) = subst_on_monotonic s m t wp; validity_substitution s hv hs in
let hscmpg2 : scmp g2 (Cmp m' (tsubst s t') (tsubst s wp')) (Cmp m (tsubst s t) (tsubst s wp)) (tsubst s (sub_computation phi m t wp m' t' wp')) = subst_on_sub_computation s phi m t wp m' t' wp'; SCmp m' (tsubst s wp') m (tsubst s wp) hsubg2 hkg2 hvg2 in
hscmpg2
*)
and styping_substitution g1 t' t phi s g2 h1 hs = match h1 with
| SubConv #g #t t' hv hk ->
admit()(*
let hvg2 : validity g2 (teqtype (tsubst s t') (tsubst s t)) = subst_on_teqtype s t t'; validity_substitution s hv hs in
let hkg2 : kinding g2 (tsubst s t) KType = kinding_substitution s hk hs in
let hsubg2 : styping g2 (tsubst s t') (tsubst s t) (tsubst s ttrue) = SubConv (tsubst s t') hvg2 hkg2 in hsubg2
*)
| SubFun #g #t #t' #phi #c' #c #psi hst hk hsc ->
admit()(*
(
let hkg1 : kinding g1 t KType = hk in
let hkg2 : kinding g2 (tsubst s t) KType = kinding_substitution s hk hs in
let hstg2 : styping g2 (tsubst s t) (tsubst s t') (tsubst s phi) = styping_substitution s hst hs in
let hscg2 : scmp (eextend (tsubst s t) g2) (csubst (sub_elam s) c') (csubst (sub_elam s) c) (tsubst (sub_elam s) psi) = scmp_substitution (sub_elam s) hsc (elam_hs s t hs) in
let hr : styping g2 (TArr (tsubst s t') (csubst (sub_elam s) c')) (TArr (tsubst s t) (csubst (sub_elam s) c)) (tand (tsubst s phi) (tforalle (tsubst s t) (tsubst (sub_elam s) psi))) = SubFun hstg2 hkg2 hscg2 in
subst_on_tforalle s t psi;
subst_on_tand s phi (tforalle t psi);
hr
)
*)
| SubTrans #g #t1 #t2 #t3 #phi12 #phi23 hs12 hs23 ->
admit()(*
SubTrans (styping_substitution s hs12 hs) (styping_substitution s hs23 hs)
*)
and tcwf_substitution g1 c s g2 h1 hs = match h1 with
|WFTcForallT #g #k hkw -> 
admit()(*
WFTcForallT (kwf_substitution s hkw hs)
*)
|WFTcEqT #g #k hkw -> 
admit()(*
WFTcEqT (kwf_substitution s hkw hs)
*)
|WFTcOther g tc -> 
admit()(*
WFTcOther g2 tc
*)
and ecwf_substitution g1 ec s g2 h1 hs = match h1 with
| WFEcFixPure #g #tx #t' #t'' #wp hkx hk' hk'' hkwp ->
(
 let hkxg2 : kinding g2 (tsubst s tx) KType = kinding_substitution s hkx hs in
 let hk'g2 : kinding g2 (tsubst s t') (KTArr (tsubst s tx) KType) = kinding_substitution s hk' hs in
 let hk''g2 : kinding g2 (tsubst s t'') (KTArr (tsubst s tx) KType) = kinding_substitution s hk'' hs in
 let hkwpg2 : kinding g2 (tsubst s wp) (KTArr (tsubst s tx) (k_pure (TEApp (tesh (tsubst s t'')) (EVar 0)))) = subst_on_k_m (sub_elam s) EfPure (TEApp (tesh t'') (EVar 0)); tsubst_elam_shift s t''; kinding_substitution s hkwp hs in
 WFEcFixPure hkxg2 hk'g2 hk''g2 hkwpg2
)
| WFEcFixOmega #g #tx #t' #wp hkx hk' hkwp ->
(
 let hkxg2 : kinding g2 (tsubst s tx) KType = kinding_substitution s hkx hs in
 let hk'g2 : kinding g2 (tsubst s t') (KTArr (tsubst s tx) KType) = kinding_substitution s hk' hs in
 let hkwpg2 : kinding g2 (tsubst s wp) (KTArr (tsubst s tx) (k_all (TEApp (tesh (tsubst s t')) (EVar 0)))) = subst_on_k_m (sub_elam s) EfAll (TEApp (tesh t') (EVar 0)); tsubst_elam_shift s t'; kinding_substitution s hkwp hs in
WFEcFixOmega hkxg2 hk'g2 hkwpg2
)
| WFEcOther g ec -> WFEcOther g2 ec
and kinding_substitution g1 t k s g2 h1 hs = match h1 with
| KVar #g x ->
admit()
(*
(
match hs with
| SubstTyping _ _ _ _ tf -> tf x
| RenamingTyping _ _ _ _ tf -> tf x
)
*)
| KConst #g #c htc ->
admit()(*
subst_on_tconst s c; KConst #g2 #(tcsubst s c) (tcwf_substitution s htc hs)
*)
| KArr #g #t1 #t2 #phi #m hk1 hk2 hkp hv ->
admit()(*
let hsext : subst_typing (sub_elam s) (eextend t1 g1) (eextend (tsubst s t1) g2) = elam_hs s t1 hs in
let hk1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk1 hs in
let hk2g2 : kinding (eextend (tsubst s t1) g2) (tsubst s t2) KType = kinding_substitution (sub_elam s) hk2 hsext in
let hkpg2 : kinding (eextend (tsubst s t1) g2) (tsubst (sub_elam s) phi) (k_m m (tsubst (sub_elam s) t2)) = subst_on_k_m (sub_elam s) m t2; kinding_substitution (sub_elam s) hkp hsext in
let hvg2 : validity (eextend (tsubst s t1) g2) (monotonic m (tsubst (sub_elam s) t2) (tsubst (sub_elam s) phi)) = subst_on_monotonic (sub_elam s) m t2 phi; validity_substitution (sub_elam s) hv hsext in
KArr #g2 #(tsubst s t1) #(tsubst (sub_elam s) t2) #(tsubst (sub_elam s) phi) #m hk1g2 hk2g2 hkpg2 hvg2
*)
| KTLam #g #k #t #k' hw hk ->
admit()
  (*
let hwg2 : kwf g2 (ksubst s k) = kwf_substitution s hw hs in
let hkg2 : kinding (textend (ksubst s k) g2) (tsubst (sub_tlam s) t) (ksubst (sub_tlam s) k') = kinding_substitution (sub_tlam s) hk (tlam_hs s k hs) in
KTLam #g2 #(ksubst s k) #(tsubst (sub_tlam s) t) #(ksubst (sub_tlam s) k') hwg2 hkg2
*)
| KELam #g #t1 #t2 #k2 hk1 hk2 ->
admit()(*
let hk1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk1 hs in
let hk2g2 : kinding (eextend (tsubst s t1) g2) (tsubst (sub_elam s) t2) (ksubst (sub_elam s) k2) = kinding_substitution (sub_elam s) hk2 (elam_hs s t1 hs) in
KELam hk1g2 hk2g2
*)
| KTApp #g #t1 #t2 #k k' hk1 hk2 hw ->
admit() (*
let hk1g2:kinding g2 (tsubst s t1) (KKArr (ksubst s k) (ksubst (sub_tlam s) k')) = kinding_substitution s hk1 hs in
let hk2g2:kinding g2 (tsubst s t2) (ksubst s k) = kinding_substitution s hk2 hs in
let hwg2:kwf g2 (ksubst_tbeta (tsubst s t2) (ksubst (sub_tlam s) k')) = ksubst_on_tbeta s t2 k'; kwf_substitution s hw hs in
KTApp #g2 #(tsubst s t1) #(tsubst s t2) #(ksubst s k) (ksubst (sub_tlam s) k') hk1g2 hk2g2 hwg2
*)
| KEApp #g #t #t' #k #e hk ht hw ->
admit()(*
let hkg2 : kinding g2 (tsubst s t) (KTArr (tsubst s t') (ksubst (sub_elam s) k)) = kinding_substitution s hk hs in
let htg2 : typing g2 (esubst s e) (tot (tsubst s t'))= subst_on_tot s t'; typing_substitution s ht hs in
let hwg2 : kwf g2 (ksubst_ebeta (esubst s e) (ksubst (sub_elam s) k)) = ksubst_on_ebeta s e k; kwf_substitution s hw hs in
let hwg2' : kinding g2 (TEApp (tsubst s t) (esubst s e)) (ksubst s (ksubst_ebeta e k)) = ksubst_on_ebeta s e k; KEApp hkg2 htg2 hwg2 in
hwg2'
*)
| KSub #g #t #k' #k #phi hk hsk hv ->
admit()(*
let plouf : kinding g2 (tsubst s t) (ksubst s k') = kinding_substitution s hk hs in
KSub #g2 #(tsubst s t) #(ksubst s k') #(ksubst s k) #(tsubst s phi) plouf (skinding_substitution #g1 s hsk hs) (validity_substitution s hv hs)
*)
(*SF : I get an error without 'plouf' : expected type (something); got type (something){refinement}. Why ?*)
(*SF : I switched to the new version of the substitution lemma because of this case ^*)
and skinding_substitution g1 k1 k2 phi s g2 h1 hs = match h1 with
| KSubRefl #g #k hw ->
 KSubRefl (kwf_substitution s hw hs)
| KSubKArr #g #k1 #k2 k1' k2' #phi1 #phi2 hs21 hkw hs12' ->
admit()
  (*
let hkg1 : kwf g1 k2 = hkw in
let hkg2 : kwf g2 (ksubst s k2) = kwf_substitution s hkg1 hs in
let hs21g2 : skinding g2 (ksubst s k2) (ksubst s k1) (tsubst s phi1) = skinding_substitution s hs21 hs in
let hs12'g2 : skinding (textend (ksubst s k2) g2) (ksubst (sub_tlam s) k1') (ksubst (sub_tlam s) k2') (tsubst (sub_tlam s) phi2) = skinding_substitution (sub_tlam s) hs12' (tlam_hs s k2 hs) in
subst_on_tforallt s k2 phi2;
subst_on_tand s phi1 (tforallt k2 phi2);
KSubKArr (ksubst (sub_tlam s) k1') (ksubst (sub_tlam s) k2') hs21g2 hkg2 hs12'g2
*)
| KSubTArr #g #t1 #t2 #k1 #k2 #phi1 #phi2 hs21 hk hs12' ->
admit()(*
let hk : kinding g1 t2 KType = hk in
let hkg2 : kinding g2 (tsubst s t2) KType = kinding_substitution s hk hs in
let hs21g2 : styping g2 (tsubst s t2) (tsubst s t1) (tsubst s phi1) = styping_substitution s hs21 hs in
let hs12'g2 : skinding (eextend (tsubst s t2) g2) (ksubst (sub_elam s) k1) (ksubst (sub_elam s) k2) (tsubst (sub_elam s) phi2) = skinding_substitution (sub_elam s) hs12' (elam_hs s t2 hs) in
let hr : skinding g2 (KTArr (tsubst s t1) (ksubst (sub_elam s) k1)) (KTArr (tsubst s t2) (ksubst (sub_elam s) k2)) (tand (tsubst s phi1) (tforalle (tsubst s t2) (tsubst (sub_elam s) phi2))) = KSubTArr hs21g2 hkg2 hs12'g2 in
subst_on_tforalle s (t2) (phi2);
subst_on_tand s phi1 (tforalle t2 phi2);
hr
*)
and kwf_substitution g1 k s g2 h1 hs = match h1 with
| WfType g -> WfType g2
| WfTArr #g #t #k' hk hw ->
admit()(*
let plouf : kinding g2 (tsubst s t) KType = (kinding_substitution s hk hs) in
WfTArr plouf (kwf_substitution (sub_elam s) hw (elam_hs s t hs))
*)
(*SF : I also need plouf here. Why ?*)
| WfKArr #g #k #k' hw hw' -> 
admit()(*
WfKArr (kwf_substitution s hw hs) (kwf_substitution (sub_tlam s) hw' (tlam_hs s k hs))
*)
and validity_substitution g1 t1 s g2 h1 hs = match h1 with
| VAssume #g e t h -> 
admit()(*
(let h2 : typing g2 (esubst s e) (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s h hs in
VAssume #g2 (esubst s e) (tsubst s t) h2)
*)
| VRedE #g #e #t #e' ht ht' hst ->
admit()(*
(
 let ht2 : typing g2 (esubst s e) (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht hs in
 let ht2' : typing g2 (esubst s e') (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht' hs in
 let hst2 : epstep (esubst s e) (esubst s e') = epstep_substitution s e e' hst in
 VRedE ht2 ht2' hst2
)
*)
| VEqReflE #g #e #t ht -> 
admit() (*
(let ht2:typing g2 (esubst s e) (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht hs in
    let hr:validity g2 (teqe (esubst s e) (esubst s e)) = VEqReflE #g2 #(esubst s e) #(tsubst s t) ht2 in
subst_on_teqe s (esubst s e) (esubst s e);hr )
*)
| VSubstE #g #e1 #e2 #t' t hv12 ht1 ht2 hk hvsub -> 
admit()(*
(
 let hv12g2 : validity g2 (teqe (esubst s e1) (esubst s e2)) = subst_on_teqe s e1 e2; validity_substitution s hv12 hs in
 let ht1g2 : typing g2 (esubst s e1) (tot (tsubst s t')) = subst_on_tot s t'; typing_substitution s ht1 hs in
 let ht2g2 : typing g2 (esubst s e2) (tot (tsubst s t')) = subst_on_tot s t'; typing_substitution s ht2 hs in
 let hkg2 : kinding (eextend (tsubst s t') g2) (tsubst (sub_elam s) t) KType = kinding_substitution (sub_elam s) hk (elam_hs s t' hs) in
 let hvsubg2 : validity g2 (tsubst_ebeta (esubst s e1) (tsubst (sub_elam s) t)) = tsubst_on_ebeta s e1 t; validity_substitution s hvsub hs in
 let hr : validity g2 (tsubst_ebeta (esubst s e2) (tsubst (sub_elam s) t)) = VSubstE (tsubst (sub_elam s) t) hv12g2 ht1g2 ht2g2 hkg2 hvsubg2 in
 tsubst_on_ebeta s e2 t; hr
)
*)
| VRedT #g #t #t' #k hk hk' hst -> 
admit()(*
(let hkg2 : kinding g2 (tsubst s t) (ksubst s k) = kinding_substitution s hk hs in
let hk'g2 : kinding g2 (tsubst s t') (ksubst s k) = kinding_substitution s hk' hs in
let hstg2 : tstep (tsubst s t) (tsubst s t') = tstep_substitution s t t' hst in
let hr : validity g2 (teqt (ksubst s k) (tsubst s t) (tsubst s t')) = VRedT hkg2 hk'g2 hstg2 in
subst_on_teqt s k t t'; hr)
*)
| VEqReflT #g #t #k hk -> 
admit()(*
(
let hkg2 : kinding g2 (tsubst s t) (ksubst s k) = kinding_substitution s hk hs in
let hr : validity g2 (teqt (ksubst s k) (tsubst s t) (tsubst s t)) = VEqReflT hkg2 in
  subst_on_teqt s k t t; hr)
*)
| VSubstT #g #t1 #t2 #k t hv12 hkw hk hvsub ->
admit()(*
(
let hv12g2 : validity g2 (teqt (ksubst s k) (tsubst s t1) (tsubst s t2)) = subst_on_teqt s k t1 t2; validity_substitution s hv12 hs in
let hkwg2 : kwf g2 (ksubst s k) = kwf_substitution s hkw hs in
let hkg2 : kinding (textend (ksubst s k) g2) (tsubst (sub_tlam s) t) KType = kinding_substitution (sub_tlam s) hk (tlam_hs s k hs) in
let hvsubg2 : validity g2 (tsubst_tbeta (tsubst s t1) (tsubst (sub_tlam s) t)) = tsubst_on_tbeta s t1 t; validity_substitution s hvsub hs in
let hr:validity g2 (tsubst_tbeta (tsubst s t2) (tsubst (sub_tlam s) t)) = VSubstT (tsubst (sub_tlam s) t) hv12g2 hkwg2 hkg2 hvsubg2 in
tsubst_on_tbeta s t2 t; hr
)
*)
| VSelAsHeap #g #h #l hth htl -> 
admit()(*
(
    let hthg2 : typing g2 (eheap h) (tot theap) = subst_on_tot s theap; typing_substitution s hth hs in
    let htlg2 : typing g2 (eloc l) (tot tref) = subst_on_tot s tref; typing_substitution s htl hs in
    let hr : validity g2 (teqe (esel (eheap h) (eloc l)) (eint (h l))) = VSelAsHeap hthg2 htlg2 in
    subst_on_esel s (eheap h) (eloc l);
    subst_on_teqe s (esel (eheap h) (eloc l)) (eint (h l));
    hr
    )
*)
| VUpdAsHeap #g #h #l #i hth htl hti -> 
admit()(*
(
 let hthg2 : typing g2 (eheap h) (tot theap) = subst_on_tot s theap; typing_substitution s hth hs in
 let htlg2 : typing g2 (eloc l) (tot tref) = subst_on_tot s tref; typing_substitution s htl hs in
 let htig2 : typing g2 (eint i) (tot tint) = subst_on_tot s tint; typing_substitution s hti hs in
 let hr:validity g2 (teqe (eupd (eheap h) (eloc l) (eint i)) (eheap (upd_heap l i h))) = VUpdAsHeap hthg2 htlg2 htig2 in
 subst_on_eupd s (eheap h) (eloc l) (eint i);
 subst_on_teqe s (eupd (eheap h) (eloc l) (eint i)) (eheap (upd_heap l i h));
 hr

)
*)
| VSelEq #g #eh #el #ei hth htl hti ->
admit()(*
(
 let hthg2 : typing g2 (esubst s eh) (tot theap) = subst_on_tot s theap; typing_substitution s hth hs in
 let htlg2 : typing g2 (esubst s el) (tot tref) = subst_on_tot s tref; typing_substitution s htl hs in
 let htig2 : typing g2 (esubst s ei) (tot tint) = subst_on_tot s tint; typing_substitution s hti hs in
 let hr : validity g2 (teqe (esel (eupd (esubst s eh) (esubst s el) (esubst s ei)) (esubst s el)) (esubst s ei)) = VSelEq hthg2 htlg2 htig2 in
 subst_on_eupd s eh el ei;
 subst_on_esel s (eupd eh el ei) el;
 subst_on_teqe s (esel (eupd eh el ei) el) ei;
 hr
 )
*)
| VSelNeq #g #eh #el #el' #ei hth htl htl' hti hv ->
admit()(*
(
 let hthg2 : typing g2 (esubst s eh) (tot theap) = subst_on_tot s theap; typing_substitution s hth hs in
 let htlg2 : typing g2 (esubst s el) (tot tref) = subst_on_tot s tref; typing_substitution s htl hs in
 let htl'g2 : typing g2 (esubst s el') (tot tref) = subst_on_tot s tref; typing_substitution s htl' hs in
 let htig2 : typing g2 (esubst s ei) (tot tint) = subst_on_tot s tint; typing_substitution s hti hs in
 let hvg2 : validity g2 (tnot (teqe (esubst s el) (esubst s el'))) = subst_on_tnot s (teqe el el') ; subst_on_teqe s el el';  validity_substitution s hv hs in
 let hr : validity g2 (teqe (esel (eupd (esubst s eh) (esubst s el') (esubst s ei)) (esubst s ei)) (esel (esubst s eh) (esubst s el))) = VSelNeq hthg2 htlg2 htl'g2 htig2 hvg2 in
 subst_on_esel s eh el;
 subst_on_eupd s eh el' ei;
 subst_on_esel s (eupd eh el' ei) ei;
 subst_on_teqe s (esel (eupd eh el' ei) ei) (esel eh el);
 hr
)
*)
| VForallIntro #g #t #phi hk hv ->
admit()(*
(
 let hkg2 : kinding g2 (tsubst s t) KType = kinding_substitution s hk hs in
 let hvg2 : validity (eextend (tsubst s t) g2) (tsubst (sub_elam s) phi) = validity_substitution (sub_elam s) hv (elam_hs s t hs) in
 let hr : validity g2 (tforalle (tsubst s t) (tsubst (sub_elam s) phi)) = VForallIntro hkg2 hvg2 in
 subst_on_tforalle s t phi;
 hr

)
*)
| VForallTypIntro #g #k #phi hkw hv ->
admit()(*
(
 let hkwg2 : kwf g2 (ksubst s k) = kwf_substitution s hkw hs in
 let hvg2 : validity (textend (ksubst s k) g2) (tsubst (sub_tlam s) phi) = validity_substitution (sub_tlam s) hv (tlam_hs s k hs) in
 let hr : validity g2 (tforallt (ksubst s k) (tsubst (sub_tlam s) phi)) = VForallTypIntro hkwg2 hvg2 in
 subst_on_tforallt s k phi;
 hr
)
*)
| VForallElim #g #t #phi #e hv ht -> 
admit()(*
(
 let hvg2 : validity g2 (tforalle (tsubst s t) (tsubst (sub_elam s) phi)) = subst_on_tforalle s t phi; validity_substitution s hv hs in
 let htg2 : typing g2 (esubst s e) (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht hs in
 let hr : validity g2 (tsubst_ebeta (esubst s e) (tsubst (sub_elam s) phi)) = VForallElim hvg2 htg2 in
 tsubst_on_ebeta s e phi;
 hr
)
*)
| VForallTypElim #g #t #k #phi hv hk -> 
admit()(*
(
 let hvg2 : validity g2 (tforallt (ksubst s k) (tsubst (sub_tlam s) phi)) = subst_on_tforallt s k phi; validity_substitution s hv hs in
 let hkg2 : kinding g2 (tsubst s t) (ksubst s k) =kinding_substitution s hk hs in
 let hr : validity g2 (tsubst_tbeta (tsubst s t) (tsubst (sub_tlam s) phi)) = VForallTypElim hvg2 hkg2 in
 tsubst_on_tbeta s t phi;
 hr
)
*)
| VAndElim1 #g #p1 #p2 hv -> 
admit()(*
(
 let hvg2 : validity g2 (tand (tsubst s p1) (tsubst s p2)) = subst_on_tand s p1 p2; validity_substitution s hv hs in
 VAndElim1 hvg2
)
*)
| VAndElim2 #g #p1 #p2 hv -> 
admit()(*
(
 let hvg2 : validity g2 (tand (tsubst s p1) (tsubst s p2)) = subst_on_tand s p1 p2; validity_substitution s hv hs in
 VAndElim2 hvg2
)
*)
| VAndIntro #g #p1 #p2 hv1 hv2 ->
admit()(*
(
 let hv1g2 : validity g2 (tsubst s p1) = validity_substitution s hv1 hs in
 let hv2g2 : validity g2 (tsubst s p2) = validity_substitution s hv2 hs in
 subst_on_tand s p1 p2 ;VAndIntro hv1g2 hv2g2
)
*)
| VExMiddle #g #t1 #t2 hk1 hk2 hv1 hv2 ->
admit()(*
(
 let hk1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk1 hs in
 let hk2g2 : kinding g2 (tsubst s t2) KType = kinding_substitution s hk2 hs in
 let hv1g2 : validity (eextend (tsubst s t1) g2) (tesh (tsubst s t2)) = tsubst_elam_shift s t2; validity_substitution (sub_elam s) hv1 (elam_hs s t1 hs) in
 let hv2g2 : validity (eextend (tnot (tsubst s t1)) g2) (tesh (tsubst s t2)) = subst_on_tnot s t1; tsubst_elam_shift s t2; validity_substitution (sub_elam s) hv2 (elam_hs s (tnot t1) hs) in 
 VExMiddle hk1g2 hk2g2 hv1g2 hv2g2
)
*)
| VOrIntro1 #g #t1 #t2 hv hk ->
admit()(*
(
 let hvg2 : validity g2 (tsubst s t1) = validity_substitution s hv hs in
 let hkg2 : kinding g2 (tsubst s t2) KType = kinding_substitution s hk hs in
 subst_on_tor s t1 t2; VOrIntro1 hvg2 hkg2
)
*)
| VOrIntro2 #g #t1 #t2 hv hk ->
admit()(*
(
 let hvg2 : validity g2 (tsubst s t2) = validity_substitution s hv hs in
 let hkg2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk hs in
 subst_on_tor s t1 t2; VOrIntro2 hvg2 hkg2
)
*)
| VOrElim #g #t1 #t2 #t3 hk1 hk2 hk3 hvor hv1 hv2 ->
admit()(*
(
 let hk1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk1 hs in
 let hk2g2 : kinding g2 (tsubst s t2) KType = kinding_substitution s hk2 hs in
 let hk3g2 : kinding g2 (tsubst s t3) KType = kinding_substitution s hk3 hs in
 let hvorg2 : validity g2 (tor (tsubst s t1) (tsubst s t2)) = subst_on_tor s t1 t2; validity_substitution s hvor hs in
 let hv1g2 : validity (eextend (tsubst s t1) g2) (tesh (tsubst s t3)) = tsubst_elam_shift s t3; validity_substitution (sub_elam s) hv1 (elam_hs s t1 hs) in
 let hv2g2 : validity (eextend (tsubst s t2) g2) (tesh (tsubst s t3)) = tsubst_elam_shift s t3; validity_substitution (sub_elam s) hv2 (elam_hs s t2 hs) in
 VOrElim hk1g2 hk2g2 hk3g2 hvorg2 hv1g2 hv2g2
)
*)
| VFalseElim #g #t hv hk ->
admit()(*
(
 let hvg2 : validity g2 tfalse = validity_substitution s hv hs in
 let hkg2 : kinding g2 (tsubst s t) KType = kinding_substitution s hk hs in
 VFalseElim hvg2 hkg2
)
*)
| VPreceedsIntro #g #v1 #v2 #t1 #t2 ht1 ht2 ->
admit()(*
(
 let ht1g2 : typing g2 (esubst s v1) (tot (tsubst s t1)) = subst_on_tot s t1; typing_substitution s ht1 hs in
 let ht2g2 : typing g2 (esubst s v2) (tot (tsubst s t2)) = subst_on_tot s t2; typing_substitution s ht2 hs in
 VPreceedsIntro ht1g2 ht2g2
)
*)
| VDistinctC g c1 c2 -> 
(subst_on_teqe s (EConst c1) (EConst c2); subst_on_tnot s (teqe (EConst c1) (EConst c2)); VDistinctC g2 (ecsubst s c1) (ecsubst s c2))
| VDistinctTH #g #t1 #t2 hk1 hk2 -> 
(
 let hk1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk1 hs in
 let hk2g2 : kinding g2 (tsubst s t2) KType = kinding_substitution s hk2 hs in
 subst_on_hnf s t1; subst_on_hnf s t2;
 subst_preserves_head_eq s t1 t2;
 let hr: validity g2 (tnot (teqtype (tsubst s t1) (tsubst s t2))) = VDistinctTH hk1g2 hk2g2 in
 subst_on_teqtype s t1 t2;
 subst_on_tnot s (teqtype t1 t2);
 hr
)
(*TODO: ^ last rule to write !*)
| VInjTH #g #t1 #t2 #phi #t1' #t2' #phi' #m hv -> 
admit()(*
(
 let hvg2 : validity g2 (teqtype (TArr (tsubst s t1) (Cmp m (tsubst (sub_elam s) t2) (tsubst (sub_elam s) phi))) (TArr (tsubst s t1') (Cmp m (tsubst (sub_elam s) t2') (tsubst (sub_elam s) phi')))) = subst_on_teqtype s (TArr t1 (Cmp m t2 phi)) (TArr t1' (Cmp m t2' phi')); validity_substitution s hv hs in
 let hr : validity g2 (tand (tand (teqtype (tsubst s t1) (tsubst s t1')) (teqtype (tforalle (tsubst s t1) (tsubst (sub_elam s) t2)) (tforalle (tsubst s t1) (tsubst (sub_elam s) t2')))) (teqtype (tforalle (tsubst s t1) (tsubst (sub_elam s) phi)) (tforalle (tsubst s t1) (tsubst (sub_elam s) phi')))) = VInjTH hvg2 in
 subst_on_tforalle s t1 t2;
 subst_on_tforalle s t1 t2';
 subst_on_tforalle s t1 phi;
 subst_on_tforalle s t1 phi';
 subst_on_teqtype s t1 t1';
 subst_on_teqtype s (tforalle t1 t2) (tforalle t1 t2');
 subst_on_teqtype s (tforalle t1 phi) (tforalle t1 phi');
 subst_on_tand s (teqtype t1 t1') (teqtype (tforalle t1 t2) (tforalle t1 t2'));
 subst_on_tand s (tand (teqtype t1 t1') (teqtype (tforalle t1 t2) (tforalle t1 t2'))) (teqtype (tforalle t1 phi) (tforalle t1 phi'));
 hr
)
*)
and elam_hs g1 s g2 t1 hs = 
admit()(*
let g1ext = eextend t1 g1 in
let g2ext = eextend (tsubst s t1) g2 in
let hs'' : subst_typing sub_einc g2 (eextend (tsubst s t1) g2) =
hs_sub_einc g2 (tsubst s t1) in
(match hs with SubstTyping s' g1' g2' ef tf ->
    SubstTyping (sub_elam s) g1ext g2ext
      (fun x -> match x with
		| 0 -> (*TyVar 0 hwg2ext -> typing g2ext (EVar 0) (tot (tesh (tsubst s t1)))
			elam_shift       -> typing g2ext (EVar 0) (tot (tsubst (sub_elam s) (tesh t1)))*)
			(tsubst_elam_shift s t1;
			 TyVar 0 )
		| n -> (
		       (*hg2   -> typing g2 (s.es (x-1)) (tot (tsubst s (g1 (x-1))))*)
		       (*ind   -> typing g2ext (eesh s.ex (x-1)) (cesh (tot (tsubst s (g1 (x-1))))) *)
		       (*subst_on_tot -> typing g2ext (eesh s.ex (x-1)) (tot (tesh (tsubst s (g1 (x-1)))))*)
		       (*elam_shift -> typing g2ext (eesh s.ex (x-1)) (tot (tsubst (sub_elam s) (tesh (g1 (x-1))))) *)
		       (* =    -> typing g2ext (esub_elam x) (tot (tsubst (sub_elam s) (g1ext x)))*)

		       let eg2 = Sub.es s (x-1) in
		       let tg1 = Some.v (lookup_evar g1 (x-1)) in
		       let hg2 : typing g2 eg2 (tot (tsubst s tg1))  = ef (x-1) in
		       let hg2ext : typing g2ext (eesh eg2) (cesh (tot (tsubst s tg1))) = typing_substitution sub_einc hg2 hs'' in
		       subst_on_tot sub_einc (tsubst s tg1);
		       tsubst_elam_shift s tg1;
		       hg2ext
		       )
      )
      (fun a ->
                let hkg2 = tf a in
		(*hkg2    -> kinding g2 (s.tf a) (ksubst s (g1 a)) *)
		let hkg2ext = kinding_substitution sub_einc hkg2 hs'' in
		(*hkg2ext -> kinding g2ext (tesh (s.tf a)) (kesh (ksubst s (g1 a)))*)
		(*elam_shift -> kinding g2ext (tesh (s.tf a)) (ksubst (sub_elam s) (kesh (g1 a)))*)
		ksubst_elam_shift s (Some.v (lookup_tvar g1 a));
		hkg2ext
      )
| RenamingTyping s' g1' g2' ef tf ->
    RenamingTyping (sub_elam s) g1ext g2ext
      (fun x -> match x with
		| 0 -> (tsubst_elam_shift s t1; TyVar 0 )
		| n -> (
		       (*x'   -> s.es (x-1) = EVar x' /\ is_Some (lookup_evar g2 x') /\ tsubst s (lookup_evar g1 (x-1)).v = (lookup_evar g2 x').v*)
		       (*ind   -> typing g2ext (eesh s.ex (x-1)) (cesh (tot (tsubst s (g1 (x-1))))) *)
		       (*subst_on_tot -> typing g2ext (eesh s.ex (x-1)) (tot (tesh (tsubst s (g1 (x-1)))))*)
		       (*elam_shift -> typing g2ext (eesh s.ex (x-1)) (tot (tsubst (sub_elam s) (tesh (g1 (x-1))))) *)
		       (* =    -> typing g2ext (esub_elam x) (tot (tsubst (sub_elam s) (g1ext x)))*)

		       let eg2 = Sub.es s (x-1) in
		       let tg1 = Some.v (lookup_evar g1 (x-1)) in
		       let hg2 : typing g2 eg2 (tot (tsubst s tg1))  = ef (x-1) in
		       let hg2ext : typing g2ext (eesh eg2) (cesh (tot (tsubst s tg1))) = typing_substitution sub_einc hg2 hs'' in
		       subst_on_tot sub_einc (tsubst s tg1);
		       tsubst_elam_shift s tg1;
		       hg2ext
		       )
      )
      (fun a ->
                let hkg2 = tf a in
		(*hkg2    -> kinding g2 (s.tf a) (ksubst s (g1 a)) *)
		let hkg2ext = kinding_substitution sub_einc hkg2 hs'' in
		(*hkg2ext -> kinding g2ext (tesh (s.tf a)) (kesh (ksubst s (g1 a)))*)
		(*elam_shift -> kinding g2ext (tesh (s.tf a)) (ksubst (sub_elam s) (kesh (g1 a)))*)
		ksubst_elam_shift s (Some.v (lookup_tvar g1 a));
		hkg2ext
      )
)
*)
and tlam_hs g1 s g2 k hs =
admit()(*
let g1ext = textend k g1 in
let g2ext = textend (ksubst s k) g2 in
let hs'' : subst_typing sub_tinc g2 g2ext = hs_sub_tinc g2 (ksubst s k) in
let newhs : subst_typing (sub_tlam s) g1ext g2ext =
(match hs with
| SubstTyping _ _ _ ef tf ->
    SubstTyping (sub_tlam s) g1ext g2ext
      (fun x -> let htg2 = ef x in
                (*htg2 : g2 |- s(x) : tot (tsubst s (g1(x)))*)
                let tg1 = Some.v (lookup_evar g1 x) in
                let htg2ext = typing_substitution sub_tinc htg2 hs'' in
                (*htg2ext : g2ext |- eesh (s(x)) : tesh (tot (tsubst s (g1(x))))*)

                subst_on_tot sub_tinc (tsubst s tg1);
                tsubst_tlam_shift s tg1;
                htg2ext
      )
      (fun a -> match a with
                | 0 -> (ksubst_tlam_shift s k; KVar 0 )
                | n -> (
		let tg2 = Sub.ts s (a-1) in
		let kg1 = Some.v (lookup_tvar g1 (a-1)) in
		let hkg2 : kinding g2 tg2 (ksubst s kg1) = tf (a-1) in
		let hkg2ext : kinding g2ext (ttsh tg2) (ktsh (ksubst s kg1)) = kinding_substitution sub_tinc hkg2 hs'' in
		ksubst_tlam_shift s kg1;
		assert(ktsh (ksubst s kg1) = ksubst (sub_tlam s) (ktsh kg1));
		hkg2ext)
      )
| RenamingTyping _ _ _ ef tf ->
    RenamingTyping (sub_tlam s) g1ext g2ext 
      (fun x -> let htg2 = ef x in
                (*htg2 : g2 |- s(x) : tot (tsubst s (g1(x)))*)
                let tg1 = Some.v (lookup_evar g1 x) in
                let htg2ext = typing_substitution sub_tinc htg2 hs'' in
                (*htg2ext : g2ext |- eesh (s(x)) : tesh (tot (tsubst s (g1(x))))*)

                subst_on_tot sub_tinc (tsubst s tg1);
                tsubst_tlam_shift s tg1;
                htg2ext
      )
      (fun a -> match a with
                | 0 -> (ksubst_tlam_shift s k; KVar 0 )
                | n -> (
		let tg2 = Sub.ts s (a-1) in
		let kg1 = Some.v (lookup_tvar g1 (a-1)) in
		let hkg2 : kinding g2 tg2 (ksubst s kg1) = tf (a-1) in
		let hkg2ext : kinding g2ext (ttsh tg2) (ktsh (ksubst s kg1)) = kinding_substitution sub_tinc hkg2 hs'' in
		ksubst_tlam_shift s kg1;
		hkg2ext)
      )

)
in newhs
*)

(**********************)
(* Derived judgements *)
(**********************)
(*
val typing_derived : #g:env -> #e:exp -> #m:eff -> #t:typ -> #wp:typ ->
                     typing g e (Cmp m t wp) ->
                     Tot (cand (cand (kinding g t KType) (kinding g wp (k_m m t))) (cand (validity g (monotonic m t wp)) (ewf g)))
val scmp_derived : #g:env -> #m':eff -> #t':typ -> #wp':typ ->
                             #m:eff -> #t:typ -> #wp:typ -> #phi:typ ->
                             scmp g (Cmp m' t' wp') (Cmp m t wp) phi ->
                             kinding g t' KType ->
                             Tot (cand (cand (kinding g t KType) (kinding g wp (k_m m t))) (cand (kinding g phi KType) (ewf g)))
*)

(* CH: TODO: How about starting directly with the substitution lemma
             and only prove what's needed for that. Could it be it
             doesn't even need derived judgments? *)

(* Derived kinding rules -- TODO: need a lot more *)

(* derived judgments (small part) *)
opaque val kinding_ewf : #g:env -> #t:typ -> #k:knd ->
                  =hk:kinding g t k ->
                 Tot (ewf g)
let kinding_ewf g t k hk = admit()

(* This takes forever to typecheck and fails without the assert;
   plus this fails without the explicit type annotation on k' in KTApp
   (Unresolved implicit argument). Filed as #237.
val k_foralle : #g:env -> #t1:typ -> #t2:typ ->
                =hk1:kinding g t1 KType ->
                =hk2:kinding (eextend t1 g) t2 KType ->
                Tot (kinding g (TTApp (TConst TcForallE) t1)
                               (KKArr (KTArr t1 KType) KType))
let k_foralle g t1 t2 hk1 hk2 =
  let gwf = kinding_ewf hk1 in
  (* assert(KKArr (KTArr t1 KType) KType =  *)
  (*        ktsubst_beta t1 (KKArr (KTArr (TVar 0) KType) KType)); *)
  KTApp (KKArr (KTArr (TVar 0) KType) KType) (KConst TcForallE gwf) hk1 (magic())
*)

val k_foralle : #g:env -> #t1:typ -> #t2:typ ->
                =hk1:kinding g t1 KType ->
                =hk2:kinding (eextend t1 g) t2 KType ->
                Tot (kinding g (tforalle t1 t2) KType)
let k_foralle g t1 t2 hk1 hk2 = admit()
(* TODO: finish this -- it takes >10s to check (admitting)
  let gwf = kinding_ewf hk1 in
  let tres x = KKArr (KTArr x KType) KType in
     (* using tres doesn't work, god damn it! Had to unfold it. File this shit. *)
  let happ1 : (kinding g (TTApp (TConst TcForallE) t1)
                         (KKArr (KTArr t1 KType) KType)) =
    KTApp (KKArr (KTArr (TVar 0) KType) KType) (KConst TcForallE gwf) hk1 (magic())
          (* (WfKArr (magic()) (\*WfTArr (magic())*\) *)
          (*                 (WfType (eextend (TVar 0) g)) *)
          (*         (WfType (textend KType g))) *)
  in magic() (* KTApp KType happ1 hk2 (WfType g) *)
*)

val k_impl : #g:env -> #t1:typ -> #t2:typ ->
            =hk1:kinding g t1 KType ->
            =hk2:kinding g t2 KType ->
            Tot (kinding g (timpl t1 t2) KType)
let k_impl g t1 t2 hk1 hk2 = admit()
(* TODO: this needs updating:
  let happ1 : (kinding g (TTApp (TConst TcImpl) t1) (KKArr KType KType)) =
    KTApp (KKArr KType KType) (KConst g TcImpl) hk1
          (WfKArr (WfType g) (WfType (textend g KType)))
  in KTApp KType happ1 hk2 (WfType g)
*)

val k_false : g:env -> Tot (kinding g tfalse KType)
let k_false g = KConst (WFTcOther g TcFalse)

val k_not : #g:env -> #t:typ ->
           =hk:kinding g t KType ->
           Tot (kinding g (tnot t) KType)
let k_not g t hk = k_impl hk (k_false g)

(* TODO: need to prove derived judgment and weakening before we can
   prove some of the derived validity rules! For us weakening is just
   an instance of (expression) substitution, so we also need
   substitution. All this works fine only if none of these proofs rely
   on things like v_of_intro1; at this point I don't see why the wouldn't. *)

(* Derived validity rules *)

(* CH: TODO: trying to encode as many logical connectives as possible
             to reduce the number of rules here (prove them as lemmas) *)

val v_impl_intro : #g:env -> t1:typ -> t2:typ ->
                   =hk:kinding g t1 KType ->
                   =hv:validity (eextend t1 g) (tesh t2) ->
                  Tot (validity g (timpl t1 t2))
let v_impl_intro g t1 t2 hk hv= VForallIntro hk hv

val v_impl_elim : #g:env -> #t1:typ -> #t2:typ ->
                 =hv12:validity g (timpl t1 t2) ->
                 =hv1 :validity g t1 ->
                  Tot (validity g t2)
let v_impl_elim = admit()

assume val v_true : #g:env -> =hewf:ewf g -> Tot (validity g ttrue)
(* VAssume changed *)
(* let v_true g hewf = v_impl_intro tfalse tfalse *)
(*                             (VAssume 0 (GType (k_false hewf))) *)

    (* CH: Can probably derive V-ExMiddle from: *)

    (* G, _:~t |= t *)
    (* ----------- [V-Classical] *)
    (* G |= t *)

    (*     of, even better, from this *)

    (* G, _:~t |= false *)
    (* --------------- [V-Classical] *)
    (* G |= t *)

(* Should follow without VExMiddle *)
val v_not_not_intro : #g:env -> #t:typ ->
                      =hv:validity g t ->
                          validity g (tnot (tnot t))
let v_not_not_intro = admit()

(* Should follow from VExMiddle (it's equivalent to it) *)
val v_not_not_elim : #g:env -> t:typ ->
                     =hv:validity g (tnot (tnot t)) ->
                         validity g t
let v_not_not_elim = admit()

(* Sketch for v_or_intro1

       g |= t1
       ------------ weakening!   ------------- VAssume
       g, ~t1 |= t1              g, ~t1 |= ~t1
       --------------------------------------- VImplElim
                 g, ~t1 |= false
                 --------------- VFalseElim
                  g, ~t1 |= t2
                 --------------- VImplIntro
                 g |= ~t1 ==> t2
 *)
val v_or_intro1 : #g:env -> #t1:typ -> #t2:typ ->
                  =hv1:validity g t1 ->
                  =hk2:kinding g t2 KType ->
                       validity g (tor t1 t2)
let v_or_intro1 g t1 t2 hv1 hk2 = magic()
  (*
  v_impl_intro (tnot t1) t2
               (magic())
	       *)

val v_or_intro2 : #g:env -> #t1:typ -> #t2:typ ->
                  =hv:validity g t2 ->
                  =hk:kinding g t1 KType ->
                      validity g (tor t1 t2)
let v_or_intro2 = admit()

(* CH: TODO: so far didn't manage to derive this on paper,
             might need to add it back as primitive! *)
val v_or_elim : #g:env -> t1:typ -> t2:typ -> #t3:typ ->
                =hv :validity g (tor t1 t2) ->
                =hv1:validity (eextend t1 g) (tesh t3) ->
                =hv2:validity (eextend t2 g) (tesh t3) ->
                =hk :kinding g t3 KType ->
                     validity g t3
let v_or_elim = admit()

(* CH: TODO: prove symmetry and transitivity of equality as in the F7
   paper from VEqRefl and VSubst; this will save us 4 rules *)

val v_eq_trane : #g:env -> #e1:exp -> #e2:exp -> #e3:exp ->
             =hv12:validity g (teqe e1 e2) ->
             =hv23:validity g (teqe e2 e3) ->
                   validity g (teqe e1 e3)
let v_eq_trane = admit()

val v_eq_syme : #g:env -> #e1:exp -> #e2:exp ->
             =hv:validity g (teqe e1 e2) ->
                 validity g (teqe e2 e1)
let v_eq_syme = admit()

val v_eq_trant : #g:env -> #t1:typ -> #t2:typ -> #t3:typ -> #k:knd ->
             =hv12:validity g (teqt k t1 t2) ->
             =hv23:validity g (teqt k t2 t3) ->
                   validity g (teqt k t1 t3)
let v_eq_trant = admit()

val v_eq_symt : #g:env -> #t1:typ -> #t2:typ -> #k:knd ->
            =hv:validity g (teqt k t1 t2) ->
                validity g (teqt k t2 t1)
let v_eq_symt = admit()
