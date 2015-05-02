module TinyFStarNew

open Classical
open FunctionalExtensionality

type var = nat
type loc = nat

type heap = loc -> Tot int

type econst =
  | EcUnit
  | EcInt : i:int -> econst
  | EcLoc : l:loc -> econst
  | EcBang
  | EcAssign
  | EcSel
  | EcUpd
  | EcHeap : h:heap -> econst

type eff =
  | EfPure
  | EfAll

type tconst =
  | TcUnit
  | TcInt
  | TcRefInt
  | TcHeap

  | TcTrue
  | TcFalse
  | TcAnd
  | TcOr
  | TcImpl

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
  | EFix : d:(option exp) -> t:typ -> ebody:exp -> exp
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

let ttrue = TConst TcTrue
let tfalse = TConst TcFalse
let tand  a b = TTApp (TTApp (TConst TcAnd)  a) b
let tor   a b = TTApp (TTApp (TConst TcOr)   a) b
let timpl a b = TTApp (TTApp (TConst TcImpl) a) b

let tforalle t p = TTApp (TTApp (TConst TcForallE) t) p
let tforallt a p = TTApp (TConst (TcForallT a)) p

let teqe e1 e2 = TEApp (TEApp (TConst TcEqE) e1) e2
let teqt k t1 t2 = TTApp (TTApp (TConst (TcForallT k)) t1) t2

let tprecedes e1 e2 = TEApp (TEApp (TConst TcPrecedes) e1) e2

(*TODO:write a function {e|t|k}shift_up which
shift both expression and type variables
and prove some properties on it*)

let tnot a = timpl a tfalse

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

val esub_inc_above : nat -> var -> Tot exp
let esub_inc_above x y = if y<x then EVar y else EVar (y+1)

val esub_inc : var -> Tot exp
let esub_inc = esub_inc_above 0

let is_evar (e:exp) : int = if is_EVar e then 0 else 1

val omap : ('a -> Tot 'b) -> option 'a -> Tot (option 'b)
let omap f o =
  match o with
  | Some x -> Some (f x)
  | None   -> None

val eesubst : s:esub -> e:exp -> Pure exp (requires True)
      (ensures (fun e' -> erenaming s /\ is_EVar e ==> is_EVar e'))
      (decreases %[is_evar e; is_erenaming s; e])
val tesubst : s:esub -> t:typ -> Tot typ
      (decreases %[1; is_erenaming s; t])
val kesubst : s:esub -> k:knd -> Tot knd
      (decreases %[1; is_erenaming s; k])

let rec eesubst s e =
  match e with
  | EVar x -> s x
  | EConst c -> e
  | ELam t e1 ->
     let esub_lam : y:var -> Tot (e:exp{erenaming s ==> is_EVar e}) =
       fun y -> if y=0 then EVar y
                else (eesubst esub_inc (s (y - 1))) in
     ELam (tesubst s t) (eesubst esub_lam e1)
  | EFix d t ebody ->
     let esub_lam2 : y:var -> Tot(e:exp{erenaming s ==> is_EVar e}) =
       fun y -> if y <= 1 then EVar y
                else (eesubst esub_inc (eesubst esub_inc (s (y-2)))) in
     let d' = match d with
              | Some de -> Some (eesubst s de)
              | None -> None in
     (* CH: wanted to write "d' = (omap (eesubst s) d)" but that fails
            the termination check *)
     EFix d' (tesubst s t) (eesubst esub_lam2 ebody)
  | EIf0 g ethen eelse -> EIf0 (eesubst s g) (eesubst s ethen) (eesubst s eelse)
  | EApp e1 e2 -> EApp (eesubst s e1) (eesubst s e2)

and tesubst s t =
  match t with
  | TVar a -> t
  | TConst c ->
     (match c with
      | TcEqT k     -> TConst (TcEqT (kesubst s k))
      | TcForallT k -> TConst (TcForallT (kesubst s k))
      | c           -> TConst c)
  | TArr t c ->
     let esub_lam : y : var -> Tot (e:exp{erenaming s ==> is_EVar e}) =
       fun y -> if y=0 then EVar y
                else eesubst esub_inc (s (y-1)) in
     TArr (tesubst s t)
          (Cmp (Cmp.m c) (tesubst esub_lam (Cmp.t c))
               (tesubst esub_lam (Cmp.wp c)))
  | TTLam k tbody -> TTLam (kesubst s k) (tesubst s tbody)
  | TELam t tbody ->
     let esub_lam : y : var -> Tot (e:exp{erenaming s ==> is_EVar e}) =
       fun y -> (*TODO: why does fstar complain when it is written
                        «y = 0» with spaces 
                  CH: can't reproduce this, what variant do you use? *)
                if y=0 then EVar y
                else (eesubst esub_inc (s (y-1))) in
     TELam (tesubst s t) (tesubst esub_lam tbody)
  | TTApp t1 t2 -> TTApp (tesubst s t1) (tesubst s t2)
  | TEApp t e -> TEApp (tesubst s t) (eesubst s e)

and kesubst s k = match k with
  | KType -> KType
  | KKArr k kbody -> KKArr (kesubst s k) (kesubst s kbody)
  | KTArr t kbody ->
     let esub_lam : y :var -> Tot(e:exp{erenaming s ==> is_EVar e}) =
       fun y -> if y = 0 then EVar y
                else (eesubst esub_inc (s (y-1))) in
     KTArr (tesubst s t) (kesubst esub_lam kbody)

val esub_lam : s:esub -> Tot esub
let esub_lam s y =
  if y = 0 then EVar y
           else eesubst esub_inc (s (y-1))

val eesubst_extensional: s1:esub -> s2:esub{FEq s1 s2} -> e:exp ->
Lemma (requires True) (ensures (eesubst s1 e = eesubst s2 e))
                       [SMTPat (eesubst s1 e);  SMTPat (eesubst s2 e)]
let eesubst_extensional s1 s2 e = ()

val tesubst_extensional: s1:esub -> s2:esub{FEq s1 s2} -> t:typ ->
Lemma (requires True) (ensures (tesubst s1 t = tesubst s2 t))
                       [SMTPat (tesubst s1 t);  SMTPat (tesubst s2 t)]
let tesubst_extensional s1 s2 t = ()

val kesubst_extensional: s1:esub -> s2:esub{FEq s1 s2} -> k:knd ->
Lemma (requires True) (ensures (kesubst s1 k = kesubst s2 k))
let kesubst_extensional s1 s2 k = ()

val eesubst_lam_hoist : t:typ -> e:exp -> s:esub -> Lemma (requires True)
      (ensures (eesubst s (ELam t e) =
                ELam (tesubst s t) (eesubst (esub_lam s) e)))
let eesubst_lam_hoist t e s = ()

val tesubst_elam_hoist : t:typ -> tbody:typ -> s:esub -> Lemma (requires True)
      (ensures (tesubst s (TELam t tbody) =
                TELam (tesubst s t) (tesubst (esub_lam s) tbody)))

let tesubst_elam_hoist t tbody s = ()

val esub_beta_gen : var -> exp -> Tot esub
let esub_beta_gen x e = fun y -> if y < x then (EVar y)
                                 else if y = x then e
                                 else (EVar (y-1))

val eesubst_beta_gen : var -> exp -> exp -> Tot exp
let eesubst_beta_gen x e' = eesubst (esub_beta_gen x e')

let eesubst_beta = eesubst_beta_gen 0

val tesubst_beta_gen : var -> exp -> typ -> Tot typ
let tesubst_beta_gen x e = tesubst (esub_beta_gen x e)

let tesubst_beta = tesubst_beta_gen 0

val kesubst_beta_gen : var -> exp -> knd -> Tot knd
let kesubst_beta_gen x e = kesubst (esub_beta_gen x e)

let kesubst_beta = kesubst_beta_gen 0

let eesh = eesubst esub_inc
let tesh = tesubst esub_inc
let kesh = kesubst esub_inc

assume val teappears_in : var -> typ -> Tot bool

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

val tsub_inc : var -> Tot typ
let tsub_inc = tsub_inc_above 0

let is_tvar (t:typ) : int = if is_TVar t then 0 else 1

val etsubst : s:tsub -> e:exp -> Tot exp
      (decreases %[1; is_trenaming s; e])
val ttsubst : s:tsub -> t:typ -> Pure typ (requires True)
      (ensures (fun t' -> trenaming s /\ is_TVar t ==> is_TVar t'))
      (decreases %[is_tvar t; is_trenaming s; t])
val ktsubst : s:tsub -> k:knd -> Tot knd
      (decreases %[1; is_trenaming s; k])

let rec etsubst s e =
  match e with
  | EVar x -> e
  | EConst c -> e
  | ELam t ebody -> ELam (ttsubst s t) (etsubst s ebody)
  | EFix d t ebody ->
     let d' = match d with
              | Some de -> Some (etsubst s de)
              | None -> None in
     EFix d' (ttsubst s t) (etsubst s ebody)
  | EIf0 g ethen eelse -> EIf0 (etsubst s g) (etsubst s ethen) (etsubst s eelse)
  | EApp e1 e2 -> EApp (etsubst s e1) (etsubst s e2)

and ttsubst s t =
  match t with
  | TVar a -> t
  | TConst c ->
     (match c with
      | TcEqT k -> TConst (TcEqT (ktsubst s k))
      | TcForallT k -> TConst (TcForallT (ktsubst s k))
      | c -> TConst c)
  | TArr t c ->
     TArr (ttsubst s t)
          (Cmp (Cmp.m c) (ttsubst s (Cmp.t c)) (ttsubst s (Cmp.wp c)))
  | TTLam k tbody ->
     let tsub_lam : y : var -> Tot (t:typ{trenaming s ==> is_TVar t}) =
       fun y -> if y=0 then TVar y
                else (ttsubst tsub_inc (s (y-1))) in
     TTLam (ktsubst s k) (ttsubst tsub_lam tbody)
  | TELam t tbody -> TELam (ttsubst s t) (ttsubst s tbody)
  | TTApp t1 t2 -> TTApp (ttsubst s t1) (ttsubst s t2)
  | TEApp t e -> TEApp (ttsubst s t) (etsubst s e)

and ktsubst s k =
  match k with
  | KType -> KType
  | KKArr k kbody ->
     let tsub_lam : y :var -> Tot(t:typ{trenaming s ==> is_TVar t}) =
       fun y -> if y = 0 then TVar y
                else (ttsubst tsub_inc (s (y-1))) in
     KKArr (ktsubst s k) (ktsubst tsub_lam kbody)
  | KTArr t kbody ->
     KTArr (ttsubst s t) (ktsubst s kbody)

val tsub_lam: s:tsub -> Tot tsub
let tsub_lam s y =
  if y = 0 then TVar y
           else ttsubst tsub_inc (s (y-1))
val etsubst_extensional: s1:tsub -> s2:tsub{FEq s1 s2} -> e:exp ->
Lemma (requires True) (ensures (etsubst s1 e = etsubst s2 e))
                       [SMTPat (etsubst s1 e);  SMTPat (etsubst s2 e)]
let etsubst_extensional s1 s2 e = ()

val ttsubst_extensional: s1:tsub -> s2:tsub{FEq s1 s2} -> t:typ ->
Lemma (requires True) (ensures (ttsubst s1 t = ttsubst s2 t))
                       [SMTPat (ttsubst s1 t);  SMTPat (ttsubst s2 t)]
let ttsubst_extensional s1 s2 t = ()

val ktsubst_extensional: s1:tsub -> s2:tsub{FEq s1 s2} -> k:knd ->
Lemma (requires True) (ensures (ktsubst s1 k = ktsubst s2 k))
let ktsubst_extensional s1 s2 k = ()

val ttsubst_tlam_hoist : k:knd -> tbody:typ -> s:tsub -> Lemma (requires True)
      (ensures (ttsubst s (TTLam k tbody) =
                TTLam (ktsubst s k) (ttsubst (tsub_lam s) tbody)))

let ttsubst_tlam_hoist t e s = ()

val tsub_beta_gen : var -> typ -> Tot tsub
let tsub_beta_gen x t = fun y -> if y < x then (TVar y)
                                 else if y = x then t
                                 else (TVar (y-1))

val ttsubst_beta_gen : var -> typ -> typ -> Tot typ
let ttsubst_beta_gen x t' = ttsubst (tsub_beta_gen x t')

val ktsubst_beta_gen : var -> typ -> knd -> Tot knd
let ktsubst_beta_gen x t' = ktsubst (tsub_beta_gen x t')

let ttsubst_beta = ttsubst_beta_gen 0

let ktsubst_beta = ktsubst_beta_gen 0

let etsh = etsubst tsub_inc
let ttsh = ttsubst tsub_inc
let ktsh = ktsubst tsub_inc

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
  | ELam _ _
  | EVar _
  | EFix _ _ _ -> true
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
              tstep (TEApp (TELam tx t) e) (tesubst_beta e t)
  | TsTBeta : k:knd ->
              t:typ ->
              t':typ ->
              tstep (TTApp (TTLam k t) t') (ttsubst_beta t' t)
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
              epstep (EApp (ELam t ebody) v) (eesubst_beta v ebody)
  | PsFix : d:option exp ->
            t:typ ->
            ebody:exp ->
            v:value ->
            epstep (EApp (EFix d t ebody) v) (eesubst_beta (EFix d t ebody)
                                                (eesubst_beta v ebody))
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
  | PsFixT : d:option exp ->
             #t:typ ->
             #t':typ ->
             ebody:exp ->
             #ht:tstep t t' ->
             epstep (EFix d t ebody) (EFix d t' ebody)
  | PsFixD : #de:exp ->
             #de':exp ->
             t:typ ->
             ebody:exp ->
             =ht:epstep de de' ->
             epstep (EFix (Some de) t ebody) (EFix (Some de') t ebody)
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
                     (Cfg h (eesubst_beta v ebody))
  | IsFix : h:heap ->
            d:option exp ->
            t:typ ->
            ebody:exp ->
            v:value ->
            eistep (Cfg h (EApp (EFix d t ebody) v))
                   (Cfg h (eesubst_beta (EFix d t ebody)
                                        (eesubst_beta v ebody)))
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

let k m = match m with
| EfPure -> k_pure
| EfAll  -> k_all

let tot t = Cmp EfPure t (TTLam (k_post_pure t)
                           (tforalle t (TELam t (TEApp (TVar 1) (EVar 0)))))

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
  (TTLam (k_post_pure a)
    (tforallt (k_post_pure (ttsh a))
      (TTLam (k_post_pure (ttsh a))
        (timpl
          ((*forall x. p1 x ==> p2 x *)
            tforalle (ttsh (ttsh a))
             (TELam (ttsh (ttsh a))
               (timpl  (TEApp (TVar 1 (*p1*)) (EVar 0))
                       (TEApp (TVar 0 (*p2*)) (EVar 0))
               )
             )
          )
          ((*wp p1 ==> wp p2*)
            timpl (TTApp (ttsh (ttsh wp)) (TVar 1))
                  (TTApp (ttsh (ttsh wp)) (TVar 0))
          )
        )
       )
     )
  )

val monotonic_all : a:typ -> wp:typ -> Tot typ
let monotonic_all a wp =
  tforallt (k_post_pure a)
  (TTLam (k_post_pure a)
    (tforallt (k_post_pure (ttsh a))
      (TTLam (k_post_pure (ttsh a))
        (
          timpl
          ((*forall x. p1 x ==> p2 x *)
            tforalle (ttsh (ttsh a))
             (TELam (ttsh (ttsh a))
               (tforalle theap
                 (TELam theap
                    (timpl  (TEApp (TEApp (TVar 1 (*p1*)) (EVar 1(*x*))) (EVar 0) )
                            (TEApp (TEApp (TVar 0 (*p2*)) (EVar 1)) (EVar 0))
                    )
                 )
               )
             )
          )
          ((*wp p1 ==> wp p2*)
            tforalle theap
            (TELam theap
              (timpl (TEApp (TTApp (ttsh (ttsh wp)) (TVar 1)) (EVar 0))
                     (TEApp (TTApp (ttsh (ttsh wp)) (TVar 0)) (EVar 0))
              )
            )
          )
        )
      )
    )
  )

let monotonic m = match m with
  | EfPure -> monotonic_pure
  | EfAll  -> monotonic_all

val op_pure : a:typ -> op:typ -> wp1:typ -> wp2:typ -> Tot typ
let op_pure a op wp1 wp2 =
  TTLam (k_post_pure a) (TTApp (TTApp (ttsh op) (TTApp (ttsh wp1) (TVar 0)))
                               (TTApp (ttsh wp2) (TVar 0)))

val op_all : a:typ -> op:typ -> wp1:typ -> wp2:typ -> Tot typ
let op_all a op wp1 wp2 =
  TTLam (k_post_all a)
    (TELam theap
      (TTApp (TTApp (tesh (ttsh op))
                    (TEApp (TTApp (tesh (ttsh wp1)) (TVar 0)) (EVar 0)))
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
  tforallt (k_post_pure a) (TTLam (k_post_pure a) (TTApp (ttsh wp) (TVar 0)))

val down_all : a : typ -> wp:typ -> Tot typ
let down_all a wp =
  tforallt (k_post_all a)
   (TTLam (k_post_all a)
     (tforalle theap
       (TELam theap
         (TEApp (TTApp (tesh (ttsh wp)) (TVar 0)) (EVar 0))
       )
     )
   )

let down m =
  match m with
  | EfPure -> down_pure
  | EfAll  -> down_all

val closee_pure : a:typ -> b:typ -> f:typ -> Tot typ
let closee_pure a b f =
  TTLam (k_post_pure a) (*p*)
  (tforalle (ttsh b)
   (TELam (ttsh b)
    (TTApp (TEApp (tesh (ttsh f)) (EVar 0)) (TVar 0))))

val closee_all : a:typ -> b:typ -> f:typ -> Tot typ
let closee_all a b f =
  TTLam (k_post_all a) (*p*)
  (TELam theap (
    (tforalle (tesh (ttsh b))
     (TELam (tesh (ttsh b))
      (TEApp (TTApp (TEApp (tesh (tesh (ttsh f))) (EVar 0)) (TVar 0))
             (EVar 1))))))

val closet_pure : a:typ -> f:typ -> Tot typ
let closet_pure a f =
  TTLam (k_post_pure a)
  (tforallt KType
   (TTLam (KType)
    (TTApp (TTApp (ttsh (ttsh f)) (TVar 0)) (TVar 1))))

val closet_all : a:typ -> f:typ -> Tot typ
let closet_all a f =
  TTLam (k_post_all a)
  (TELam theap
    (tforallt KType
     (TTLam (KType)
      (TEApp (TTApp (TTApp (ttsh (tesh (ttsh f))) (TVar 0)) (TVar 1)) (EVar 0)))))

val ite_pure : a:typ -> wp0:typ -> wp1:typ -> wp2:typ -> Tot typ
let ite_pure a wp0 wp1 wp2 =
  bind_pure tint a wp0
  (
   TELam (tint)
    (
      op_pure (tesh a) (TConst TcAnd)
      ((*up (i=0) ==> wp1*)
       op_pure (tesh a) (TConst TcImpl)
        (
         up_pure (tesh a)
           (teqe (EVar 0) (eint 0))
        )
         wp1
      )
      ((*up (i!=0) ==> wp2*)
       op_pure (tesh a) (TConst TcImpl)
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
      op_all (tesh a) (TConst TcAnd)
      ((*up (i=0) ==> wp1*)
       op_all (tesh a) (TConst TcImpl)
        (
         up_all (tesh a)
           (teqe (EVar 0) (eint 0))
        )
         wp1
      )
      ((*up (i!=0) ==> wp2*)
       op_all (tesh a) (TConst TcImpl)
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
  tforalle (theap) (TELam (theap) (TEApp (tesh p) (EVar 0)))

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
  op_pure t'' (TConst TcAnd)
          (up_pure (t'') (TEApp (TEApp (TConst TcPrecedes) (EApp d (EVar 0)))
                                (EApp d (EVar 1)))) wp

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
  | TcTrue
  | TcFalse     -> KType

  | TcAnd
  | TcOr
  | TcImpl      -> KKArr KType (KKArr KType KType)

  | TcForallE   -> KKArr KType (KKArr (KTArr (TVar 0) KType) KType)

  | TcEqE       -> KKArr KType (KTArr (TVar 0) (KTArr (TVar 0) KType))

  | TcPrecedes  -> KKArr KType (KKArr KType
                                 (KTArr (TVar 0) (KTArr (TVar 1) KType)))

  | TcEqT     k -> KKArr k (KKArr k KType)
  (* CH: don't we need to do some shifting for the second k in TcEqT? *)

  | TcForallT k -> KKArr (KKArr k KType) KType

let cmp_bang x =
  Cmp EfAll tint (TTLam (k_post_all tint) (TELam theap
                   (TEApp (TEApp (TVar 1) (esel (EVar 0) x)) (EVar 0))))

let cmp_assign x y =
  Cmp EfAll tunit (TTLam (k_post_all tunit) (TELam theap
                    (TEApp (TEApp (TVar 1) eunit) (eupd (EVar 0) x y))))

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

(***********************)
(* Head normal forms   *)
(***********************)

val head_const : t:typ -> Tot (option tconst)
let rec head_const t =
  match t with
  | TConst tc  -> Some tc
  | TTApp t1 _
  | TEApp t1 _ -> head_const t1
  | _          -> None

val is_hnf : typ -> Tot bool
let is_hnf t = is_TArr t || is_Some (head_const t)

val head_eq : t1:typ{is_hnf t1} -> t2:typ{is_hnf t2} -> Tot bool
let head_eq t1 t2 =
  match t1, t2 with
  | TArr _ (Cmp EfPure _ _), TArr _ (Cmp EfPure _ _)
  | TArr _ (Cmp EfAll  _ _), TArr _ (Cmp EfAll  _ _) -> true
  | _, _ -> is_Some (head_const t1) && head_const t1 = head_const t2

val head_neq : typ -> typ -> Tot bool
let head_neq t1 t2 = is_hnf t1 && is_hnf t2 && not (head_eq t1 t2)

(* CH: TODO: Implement this using head_neq
    G |- t1 : Type
    G |- t2 : Type
    t1 <>_head t2
    -------------------------------------------- [V-DistinctTH]
    G |= ~(t1 =_Type t2)

For injectivity should probably stick with this:

    G |= x:t1 -> M t2 phi = x:t1' -> M t2' phi'
    -------------------------------------------- [V-InjTH]
    G |= (t1 = t1) /\ (t2 = t2') /\ (phi = phi')

 *)

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
(* CH: TODO: Even under this assumption, I would expect that the shift
       of the binders in the env needs to be propagated to all the
       entries in the env that depend on the shifted bindings *)
val eextend : env -> typ -> Tot env
let eextend e t =
  let Env eenvi tenvi = e in
  let eenvi' : eenv = fun x -> if x = 0 then Some t
                               else eenvi (x-1)
  in enveshift (Env eenvi' tenvi)

val textend : env -> knd -> Tot env
let textend e k =
  let Env eenvi tenvi = e in
  let tenvi' : tenv = fun x -> if x = 0 then Some k
                               else tenvi (x-1)
  in envtshift (Env eenvi tenvi')

val lookup_evar : env -> var -> Tot (option typ)
let lookup_evar g x = Env.e g x

val lookup_tvar : env -> var -> Tot (option knd)
let lookup_tvar g x = Env.t g x

(**************)
(*   Typing   *)
(**************)

(* CH: TODO: I was actually hoping of getting rid of ewf completely,
       and perform few checks that still make sense in a nameless
       setting on lookups. This worked very well for lambda_omega! *)

type typing : env -> exp -> cmp -> Type =

| TyVar : #g:env ->
           x:var{is_Some (lookup_evar g x)} ->
          =h:(ewf g) ->
           typing g (EVar x) (tot (Some.v (lookup_evar g x)))

| TyConst : #g:env ->
            =h:(ewf g) ->
             c:econst ->
             typing g (EConst c) (tot (econsts c))

| TyAbs : #g:env ->
          #t1:typ ->
          #ebody:exp ->
          #m:eff ->
          #t2:typ ->
          #wp:typ -> 
          =hk:(kinding g t1 KType) -> 
           typing (eextend g t1) ebody (Cmp m t2 wp) ->
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
(*TODO: check and finish this rule. Do not use it like that !!!*)
| TyFix : g:env -> tx:typ -> t':typ -> d:exp -> t'':typ -> wp:typ -> ebody:exp ->
          kinding g (TArr tx (Cmp EfPure t'' wp)) KType ->
          typing g d (tot (TArr tx (tot t'))) ->
          typing (eextend (eextend g tx)
                          (tesh (TArr tx (Cmp EfPure t'' (tfix_wp tx t'' d wp)))))
                 ebody (Cmp EfPure (tesh t'') (tesh wp)) ->
          typing g (EFix (Some d) (TArr tx (Cmp EfPure t'' wp)) ebody)
                 (tot (TArr tx (Cmp EfPure t'' wp)))

| TyFixOmega : g:env -> tx:typ -> t':typ -> wp:typ -> ebody : exp ->
              kinding g (TArr tx (Cmp EfAll t' wp)) KType ->
              typing (eextend (eextend g tx) (tesh (TArr tx (Cmp EfAll t' wp))))
                     ebody (Cmp EfAll (tesh t') (tesh wp)) ->
              typing g (EFix None (TArr tx (Cmp EfAll t' wp)) ebody)
                     (tot (TArr tx (Cmp EfAll t' wp) ))
(* SF:for this one, is t=y:tx -> Pure t'' wp a syntactic equivalence ?
      I guess no. But where is the equivalence definition ?
   CH: It it syntactic equality. We can probably get rid of it with
       testers and selectors. *)

| TyIf0 : g:env -> e0 : exp -> e1:exp -> e2:exp -> m:eff ->
          t:typ -> wp0 : typ -> wp1 : typ -> wp2:typ -> 
          typing g e0 (Cmp m tint wp0) -> 
          typing g e1 (Cmp m t wp1) -> 
          typing g e2 (Cmp m t wp2) -> 
          typing g (EIf0 e0 e1 e2) (Cmp m t (ite m t wp0 wp1 wp2))

| TApp : g:env -> e1:exp -> e2:exp -> m:eff -> t:typ ->
         t':typ -> wp : typ -> wp1:typ -> wp2:typ  ->
         typing g e1 (Cmp m (TArr t (Cmp m t' wp)) wp1) ->
         typing g e2 (Cmp m t wp2) ->
         kinding g (tesubst_beta e2 t') KType ->
         htot:option (typing g e2 (tot t)){teappears_in 0 t' ==> is_Some htot} ->
         typing g (EApp e1 e2) (Cmp m (tesubst_beta e2 t')
                                    (bind m (TArr t (Cmp m t' wp)) t wp1 wp2))

| TyRet : g:env -> e:exp -> t:typ ->
         typing g e (tot t) ->
         typing g e (Cmp EfPure t (return_pure t e))

and scmp : g:env -> c1:cmp -> c2:cmp -> phi:typ -> Type =

| SCmp : #g:env -> m':eff -> #t':typ -> wp':typ ->
          m:eff{eff_sub m' m} -> #t:typ -> wp:typ -> #phi:typ ->
         =hs:(styping g t' t phi) ->
         =hk:(kinding g wp (k m t)) ->
         =hv:(validity g (monotonic m t wp)) ->
          scmp g (Cmp m' t' wp') (Cmp m t wp)
                 (tand phi (down m t (op m t (TConst TcImpl)
                                         wp (lift m' m t' wp'))))

and styping : g:env -> t':typ -> t:typ -> phi : typ -> Type =

| SubConv : #g:env -> #t:typ -> t':typ ->
            =hv:(validity g (teqt KType t' t)) ->
            =hk:(kinding g t KType) ->
             styping g t' t ttrue

| SubFun : #g:env -> #t:typ -> #t':typ -> #phi:typ ->
           #c':cmp -> #c:cmp -> #psi:typ ->
           =hst:(styping g t t' phi) ->
           =hsc:(scmp (eextend g t) c' c psi) ->
            styping g (TArr t' c') (TArr t c)
                      (tand phi (tforalle t (TELam t psi)))

| SubTrans : #g:env -> #t1:typ -> #t2:typ -> #t3:typ ->
             #phi12:typ -> #phi23:typ ->
             =hs12:(styping g t1 t2 phi12) ->
             =hs23:(styping g t2 t3 phi23) ->
              styping g t1 t3 (tand phi12 phi23)

and kinding : g:env -> t : typ -> k:knd -> Type =

| KVar : g:env -> x:var{is_Some (lookup_tvar g x)} ->
         ewf g ->
         kinding g (TVar x) (Some.v (lookup_tvar g x))

| KConst : g:env -> c:tconst ->
           ewf g ->
           kinding g (TConst c) (tconsts c)

| KArr : g:env -> t1:typ -> t2:typ -> phi:typ -> m:eff ->
         kinding g t1 KType ->
         kinding (eextend g t1) t2 KType ->
         kinding (eextend g t1) phi (k m t2) ->
         validity (eextend g t1) (monotonic m t2 phi) ->
         kinding g (TArr t1 (Cmp m t2 phi)) KType

| KTLam : g:env -> k:knd -> t:typ -> k':knd ->
          kwf g k ->
          kinding (textend g k) t k' ->
          kinding g (TTLam k t) (KKArr k k')

| KELam : g:env -> t1:typ -> t2:typ -> k2:knd ->
          kinding g t1 KType ->
          kinding (eextend g t1) t2 k2 ->
          kinding g (TELam t1 t2) (KTArr t1 k2)

| KTApp : g:env -> t1:typ -> t2:typ -> k:knd -> k':knd ->
          kinding g t1 (KKArr k k') ->
          kinding g t2 k ->
          kwf g (ktsubst_beta t2 k') ->
          kinding g (TTApp t1 t2) (ktsubst_beta t2 k')

| KEApp : g:env -> t:typ -> t':typ -> k:knd -> e:exp ->
          kinding g t (KTArr t' k) ->
          typing g e (tot t') ->
          kwf g (kesubst_beta e k) ->
          kinding g (TEApp t e) (kesubst_beta e k)

| KSub  : g:env -> t:typ -> k':knd -> k:knd -> phi:typ ->
          kinding g t k' ->
          skinding g k' k phi ->
          validity g phi ->
          kinding g t k

and skinding : g:env -> k1:knd -> k2:knd -> phi:typ -> Type=

| KSubRefl : g:env -> k:knd ->
             kwf g k ->
             skinding g k k ttrue

| KSubKArr : g:env -> k1:knd -> k2:knd -> k1':knd -> k2':knd ->
             phi1:typ -> phi2:typ-> 
             skinding g k2 k1 phi1 -> 
             skinding (textend g k2) k1' k2' phi2 -> 
             skinding g (KKArr k1 k1') (KKArr k2 k2')
                      (tand phi1 (tforallt k2 (TTLam k2 phi2)))

| KSubTArr : g:env -> t1:typ -> t2:typ -> k1:knd ->
             k2:knd -> phi1:typ -> phi2:typ ->
             styping g t2 t1 phi1 ->
             skinding (eextend g t2) k1 k2 phi2 ->
             skinding g (KTArr t1 k1) (KTArr t2 k2)
                      (tand phi1 (tforalle t2 (TELam t2 phi2)))

and kwf : env -> knd -> Type =

| KOkType : g:env ->
            ewf g ->
            kwf g KType

| KOkTArr : g:env -> t:typ -> k':knd ->
            kinding g t KType ->
            kwf (eextend g t) k' ->
            kwf g (KTArr t k')

| KOkKArr : g:env -> k:knd -> k':knd ->
            kwf g k ->
            kwf (textend g k) k' ->
            kwf g (KKArr k k')

and validity : g:env -> t:typ -> Type =

| VAssume : g:env -> x:var{is_Some (lookup_evar g x)} ->
            ewf g ->
            validity g (Some.v (lookup_evar g x))

| VRedE   : g:env -> e:exp -> t:typ -> e':exp ->
            typing g e (tot t) ->
            typing g e' (tot t) ->
            epstep e e' ->
            validity g (teqe e e')

| VEqReflE : g:env -> e:exp -> t:typ ->
             typing g e (tot t) ->
             validity g (teqe e e)

| VEqTranE : g:env -> e1:exp -> e2:exp -> e3:exp ->
             validity g (teqe e1 e2) ->
             validity g (teqe e2 e3) ->
             validity g (teqe e1 e3)

| VEqSymE  : g:env -> e1:exp -> e2:exp ->
             validity g (teqe e1 e2) ->
             validity g (teqe e2 e1)

(*Do we really need this rule for all x ?*)
| VSubstE  : g:env -> e1:exp -> e2:exp -> t:typ -> x:var ->
             validity g (teqe e1 e2) ->
             validity g (tesubst_beta_gen x e1 t) ->
             validity g (tesubst_beta_gen x e2 t)

| VRedT    : g:env -> t:typ -> t':typ -> k:knd ->
             kinding g t k ->
             kinding g t' k ->
             tstep t t' ->
             validity g (teqt k t t')

| VEqReflT : g:env -> t:typ -> k:knd ->
             kinding g t k ->
             validity g (teqt k t t)

| VEqTranT : g:env -> t1:typ -> t2:typ -> t3:typ -> k:knd ->
             validity g (teqt k t1 t2) ->
             validity g (teqt k t2 t3) ->
             validity g (teqt k t1 t3)

| VEqSymT : g:env -> t1:typ -> t2:typ -> k:knd ->
            validity g (teqt k t1 t2) ->
            validity g (teqt k t2 t1)

| VSubstT : g:env -> t1:typ -> t2:typ -> k:knd -> t:typ -> x:var ->
            validity g (teqt k t1 t2) ->
            validity g (ttsubst_beta_gen x t1 t) ->
            validity g (ttsubst_beta_gen x t2 t)

| VSelAsHeap : g:env -> h:heap -> l:loc ->
               typing g (eheap h) (tot theap) ->
               typing g (eloc l) (tot tref) ->
               validity g (teqe (esel (eheap h) (eloc l)) (eint (h l)))

| VUpdAsHeap : g:env -> h:heap -> l:loc -> i:int ->
               typing g (eheap h) (tot theap) ->
               typing g (eloc l) (tot tref) ->
               typing g (eint i) (tot tint) ->
               validity g (teqe (eupd (eheap h) (eloc l) (eint i))
                                (eheap (upd_heap l i h)))

| VSelEq : g:env -> eh:exp -> el:exp -> ei:exp ->
           typing g eh (tot theap) ->
           typing g el (tot tref) ->
           typing g ei (tot tint) ->
           validity g (teqe (esel (eupd eh el ei) el) ei)

| VSelNeq : g:env -> eh:exp -> el:exp -> el':exp -> ei:exp ->
            typing g eh (tot theap) ->
            typing g el (tot tref) ->
            typing g el' (tot tref) ->
            typing g ei (tot tint) ->
            validity g (tnot (teqe el el')) ->
            validity g (teqe (esel (eupd eh el' ei) ei) (esel eh el))

| VForallIntro : g:env -> t:typ -> phi:typ ->
                 validity (eextend g t) phi ->
                 validity g (tforalle t (TELam t phi))

| VForallTypIntro : g:env -> k:knd -> phi:typ ->
                    validity (textend g k) phi ->
                    validity g (tforallt k (TTLam k phi))

| VForallElim : g:env -> t:typ -> phi:typ -> e:exp ->
                validity g (tforalle t (TELam t phi)) ->
                typing g e (tot t) ->
                validity g (tesubst_beta e phi)

| VForallTypElim : g:env -> t:typ -> k:knd -> phi:typ ->
                   validity g (tforallt k (TTLam k phi)) ->
                   kinding g t k ->
                   validity g (ttsubst_beta t phi)

| VAndElim1 : g:env -> p1:typ -> p2:typ ->
              validity g (tand p1 p2) ->
              validity g p1

| VAndElim2 : g:env -> p1:typ -> p2:typ ->
              validity g (tand p1 p2) ->
              validity g p2

| VAndIntro : g:env -> p1:typ -> p2:typ ->
              validity g p1 ->
              validity g p2 ->
              validity g (tand p1 p2)

(* t1==>t2 is not a form of lambda regarding de Bruijn indices, right ?*)
| VImplIntro : g:env -> t1:typ -> t2:typ ->
               validity (eextend g t1) (tesh t2) -> (*so we have to shift t2 as well*)
               kinding g (timpl t1 t2) KType ->
               validity g (timpl t1 t2)

| VImplElim : g:env -> t1:typ -> t2:typ ->
              validity g (timpl t1 t2) ->
              validity g t1 ->
              validity g t2

| VExMiddle : g:env -> t:typ ->
              ewf g ->
              validity g (tor t (tnot t))

| VOrIntro1 : g:env -> t1:typ -> t2:typ ->
              validity g t1 ->
              kinding g t2 KType ->
              validity g (tor t1 t2)

| VOrIntro2 : g:env -> t1:typ -> t2:typ ->
              validity g t2 ->
              kinding g t1 KType ->
              validity g (tor t1 t2)

| VOrElim : g:env -> t1:typ -> t2:typ -> t3:typ ->
            validity (eextend g t1) (tesh t3) ->
            validity (eextend g t2) (tesh t3) ->
            kinding g t3 KType ->
            validity g t3

| VTrue : g:env ->
          ewf g ->
          validity g ttrue

| VFalseElim : g:env -> t:typ ->
               validity g tfalse ->
               kinding g t KType ->
               validity g t

| VDistinctC : g:env -> c1:econst -> c2:econst{c1 <> c2} -> t:typ ->
               validity g (tnot (teqe (EConst c1) (EConst c2)))

(*Where is << defined ?*)
(*| VPreceedsIntro ????*)
(*| VDistinctTH *)

and ewf : env -> Type =

| GEmpty : ewf empty

| GType  : g:env -> t:typ ->
           kinding g t KType ->
           ewf (eextend g t)

| GKind  : g:env -> k:knd ->
           kwf g k ->
           ewf (textend g k)
