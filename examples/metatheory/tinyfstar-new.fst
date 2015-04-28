module TinyFStarNew
open Classical
open FunctionalExtensionality
type var = nat
type loc = nat

type econst =
  | EcUnit
  | EcInt : int -> econst
  | EcLoc : loc -> econst
  | EcBang
  | EcAssign
  | EcSel
  | EcUpd

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

  | TcEqE

  | TcPrecedes
type knd =
  | KTyp : knd
  | KKArr : k:knd -> kbody:knd -> knd
  | KTArr : t:typ -> kbody:knd -> knd
and typ =
  | TVar : a:var -> typ
  | TConst : c:tconst -> typ

  | TArr  : t:typ -> c:cmp -> typ
  | TTLam : k:knd -> tbody:typ -> typ
  | TELam : t:typ -> tbody:typ -> typ
  | TTApp : t1:typ -> t2:typ -> typ
  | TEApp : t:typ -> e:exp -> typ
  | TEqT  : k:knd -> typ
  | TForallT : k:knd -> typ

and exp = 
  | EVar : x:var -> exp
  | EConst : c:econst -> exp
  | ELam : t:typ -> ebody:exp -> exp
  | EFix : d:(option exp) -> t:typ -> ebody : exp -> exp
  | EIf0 : g:exp -> ethen:exp -> eelse:exp -> exp
  | EApp : e1:exp -> e2:exp -> exp
and eff =
  | EfPure
  | EfAll
and cmp =
  | Cmp : m:eff -> t:typ -> wp:typ -> cmp

(****************************)
(* Expression Substitutions *)
(****************************)
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

val eesubst : s:esub -> e:exp -> Pure exp (requires True)
      (ensures (fun e' -> erenaming s /\ is_EVar e ==> is_EVar e'))
      (decreases %[is_evar e; is_erenaming s; e])
val tesubst : s:esub -> t:typ -> Tot typ
      (decreases %[1;is_erenaming s; t])
val kesubst : s:esub -> k:knd -> Tot knd
      (decreases %[1;is_erenaming s; k])
      (*
and exp = 
  | EVar : x:var -> exp
  | EConst : c:econst -> exp
  | ELam : t:typ -> ebody:exp -> exp
  | EFix : d:(option exp) -> t:typ -> ebody : exp -> exp
  | EIf0 : g:exp -> ethen:exp -> eelse:exp -> exp
  *)
let rec eesubst s e =
  match e with
  | EVar x -> s x
  | EConst c -> e
  | ELam t e1 ->
     let esub_lam : y:var -> Tot (e:exp{erenaming s ==> is_EVar e}) =
       fun y -> if y=0 then EVar y
                       else (eesubst esub_inc (s (y - 1))) in
     ELam (tesubst s t) (eesubst esub_lam e1)
  | EFix d t ebody -> let esub_lam2 : y:var -> Tot(e:exp{erenaming s ==> is_EVar e}) = fun y -> if y <= 1 then EVar y else (eesubst esub_inc (eesubst esub_inc (s (y-2)))) in
 let d' = match d with Some de -> Some (eesubst s de) | None -> None in
 EFix d' (tesubst s t) (eesubst esub_lam2 ebody)
  | EIf0 g ethen eelse -> EIf0 (eesubst s g) (eesubst s ethen) (eesubst s eelse)
  | EApp e1 e2 -> EApp (eesubst s e1) (eesubst s e2)

and tesubst s t = match t with
| TVar a -> t
| TConst c -> t
| TArr t c -> 
  let esub_lam : y : var -> Tot (e:exp{erenaming s ==> is_EVar e}) =
    fun y -> if y=0 then EVar y
             else (eesubst esub_inc (s (y-1))) in
  TArr (tesubst s t) (Cmp (Cmp.m c) (tesubst esub_lam (Cmp.t c)) (tesubst esub_lam (Cmp.wp c)))
| TTLam k tbody -> TTLam (kesubst s k) (tesubst s tbody)
| TELam t tbody -> 
  let esub_lam : y : var -> Tot (e:exp{erenaming s ==> is_EVar e}) =
    fun y -> if y=0 then EVar y (*TODO: why does fstar complain when it is written «y = 0» with spaces*)
             else (eesubst esub_inc (s (y-1))) in
TELam (tesubst s t) (tesubst esub_lam tbody)
| TTApp t1 t2 -> TTApp (tesubst s t1) (tesubst s t2)
| TEApp t e -> TEApp (tesubst s t) (eesubst s e)  
| TEqT k -> TEqT (kesubst s k)
| TForallT k -> TForallT (kesubst s k)
  (*| KTyp : knd
  | KKArr : k:knd -> kbody:knd -> knd
  | KTArr : t:typ -> kbody:knd -> knd*)

and kesubst s k = match k with 
| KTyp -> KTyp
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
      (ensures (eesubst s (ELam t e) = ELam (tesubst s t) (eesubst (esub_lam s) e)))
      (* [SMTPat (esubst (ELam t e) s)]
      (\* -- this increases running time by 10 secs and adds variability *\) *)
let eesubst_lam_hoist t e s = ()

val tesubst_elam_hoist : t:typ -> tbody:typ -> s:esub -> Lemma (requires True)
      (ensures (tesubst s (TELam t tbody) = TELam (tesubst s t) (tesubst (esub_lam s) tbody)))

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
      (decreases %[is_tvar t;is_trenaming s; t])
val ktsubst : s:tsub -> k:knd -> Tot knd
      (decreases %[1;is_trenaming s; k])

let rec etsubst s e =
  match e with
  | EVar x -> e
  | EConst c -> e
  | ELam t ebody -> ELam (ttsubst s t) (etsubst s ebody)
  | EFix d t ebody -> let d' = match d with Some de -> Some (etsubst s de) | None -> None in EFix d' (ttsubst s t) (etsubst s ebody)
  | EIf0 g ethen eelse -> EIf0 (etsubst s g) (etsubst s ethen) (etsubst s eelse)
  | EApp e1 e2 -> EApp (etsubst s e1) (etsubst s e2)

and ttsubst s t = match t with
| TVar a -> t
| TConst c -> t
| TArr t c -> 
  TArr (ttsubst s t) (Cmp (Cmp.m c) (ttsubst s (Cmp.t c)) (ttsubst s (Cmp.wp c)))
| TTLam k tbody -> 
  let tsub_lam : y : var -> Tot (t:typ{trenaming s ==> is_TVar t}) =
    fun y -> if y=0 then TVar y 
             else (ttsubst tsub_inc (s (y-1))) in
TTLam (ktsubst s k) (ttsubst tsub_lam tbody)
| TELam t tbody -> TELam (ttsubst s t) (ttsubst s tbody)
| TTApp t1 t2 -> TTApp (ttsubst s t1) (ttsubst s t2)
| TEApp t e -> TEApp (ttsubst s t) (etsubst s e)  
| TEqT k -> TEqT (ktsubst s k)
| TForallT k -> TForallT (ktsubst s k)
  (*| KTyp : knd
  | KKArr : k:knd -> kbody:knd -> knd
  | KTArr : t:typ -> kbody:knd -> knd*)
and ktsubst s k = match k with 
| KTyp -> KTyp
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
      (ensures (ttsubst s (TTLam k tbody) = TTLam (ktsubst s k) (ttsubst (tsub_lam s) tbody)))

let ttsubst_tlam_hoist t e s = ()

val tsub_beta_gen : var -> typ -> Tot tsub
let tsub_beta_gen x t = fun y -> if y < x then (TVar y)
                                 else if y = x then t
                                 else (TVar (y-1))

val ttsubst_beta_gen : var -> typ -> typ -> Tot typ
let ttsubst_beta_gen x t' = ttsubst (tsub_beta_gen x t')

let ttsubst_beta = ttsubst_beta_gen 0
(*************************************)
(*   Common substitution functions   *)
(*************************************)


val eshift_up_above : ei:nat -> ti:nat ->
                      eplus:nat -> tplus:nat ->
                      e:exp -> Tot exp
val tshift_up_above : ei:nat -> ti:nat ->
                      eplus:nat -> tplus:nat ->
                      t:typ -> Tot typ
val kshift_up_above : ei:nat -> ti:nat ->
                      eplus:nat -> tplus:nat ->
                      t:typ -> Tot typ
                      
(************************************)
(*     type manipulation functions  *)
(************************************)
let theap = TConst TcHeap
let tint = TConst TInt
let tand a b = TTApp (TTApp (TConst TcAnd) a) b

val timpl : a:typ -> b:typ -> Tot typ (*a ==> b*)
let timpl a b =
TEApp (TEApp (TConst TcImpl) a) b

val tforalle : t:typ -> p:typ -> Tot typ
let tforalle t p =
TTApp (TTApp (TConst TcForall) t) p

val tforallk : a:knd -> p:typ -> Tot typ
let tforallk a p =
TTApp (TForallT a) p
TTApp (TTApp (TConst TcForallE) a) p
(*TODO:write a function {e|t|k}shift_up which 
shift both expression and type variables
and prove some properties on it*)

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
  | ELet _ _ _
  | EIf0 _ _ _ -> false
  | EApp e1 e2 ->
      if not (is_value e2) then false
      else
      (match e1 with 
      | EApp e11 e12 -> if not (is_value e2) then false
                        else
			(match e11 with 
	                | EApp e111 e112 -> (match e111 with
			                    | EConst c -> is_EcUpd c && is_value e112(*Why is it a value ?*)
					    | _ -> false)
			| EConst c -> is_EcUpd c || is_EcSel c
			| _ -> false)
      | EConst c -> is_EcUpd c || is_EcSel c || is_EcAssign c
      | _ -> false)
        
type value = e:exp{is_value e}
type heap = loc -> Tot value

type tstep : typ -> typ -> Type =
  | TsEBeta : tx:typ ->
              t:typ ->
              e:exp ->
              tstep (TEApp (TELam tx t) e) (tesubst_beta e t)
  | TsTBeta : k:knd ->
              t:typ ->
              t':typ ->
              tstep (TTApp (TTLam k t) t') (ttsubst_beta t' t)
  | TsArrT1 : t1:typ->
              t1':typ->
	      c:cmp ->
	      ht:tstep t1 t1' ->
	      tstep (TArr t1 c) (TArr t1' c)
  | TsTAppT1 : t1:typ ->
               t1':typ ->
	       t2 : typ ->
	       ht:tstep t1 t1' ->
	       tstep (TTApp t1 t2) (TTApp t1' t2)
  | TsTAppT2 : t1:typ ->
               t2:typ ->
	       t2':typ ->
	       ht:tstep t2 t2' ->
	       tstep (TTApp t1 t2) (TTApp t1 t2') 
  | TsEAppT : t:typ ->
              t':typ ->
	      e:exp ->
	      ht:tstep t t' ->
	      tstep (TEApp t e) (TEApp t' e)
  | TsEAppE : t:typ ->
              e:exp ->
	      e':exp ->
	      estep e e' ->
	      tstep (TEApp t e) (TEApp t e')
  | TsTLamT : k:knd ->
              t:typ ->
	      t':typ ->
	      ht:tstep t t' ->
	      tstep (TTLam k t) (TTLam k t')
  | TsELamT : t1:typ ->
              t1':typ ->
	      t2:typ ->
	      ht:tstep t1 t1' ->
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
	    epstep (EApp (EFix d t ebody) v) (eesubst_beta (EFix d t ebody) (eesubst_beta v ebody))
            
  | PsIf0 :  e1:exp ->
             e2:exp ->
             epstep (EIf0 (EConst (EcInt 0)) e1 e2) e1
  | PsIfS : i:int{i<>0} ->
             e1:exp ->
             e2:exp ->
             epstep (EIf0 (EConst (EcInt i)) e1 e2) e2
  | PsAppE1 : e1:exp ->
              e1':exp ->
	      e2:exp ->
	      ht:epstep e1 e1' ->
	      epstep (EApp e1 e2) (EApp e1' e2)
  | PsAppE2 : e1:exp ->
              e2:exp ->
	      e2':exp ->
	      ht:epstep e2 e2' ->
	      epstep (EApp e1 e2) (EApp e1 e2')
  | PsLamT : t:typ ->
             t':typ ->
	     ebody:exp ->
	     tstep t t' ->
	     epstep (ELam t ebody) (ELam t' ebody)
  | PsFixT : d:option exp ->
             t:typ ->
	     t':typ ->
             ebody:exp ->
	     ht:tstep t t' ->
	     epstep (EFix d t ebody) (EFix d t' ebody)
  | PsFixD : de:exp ->
             de':exp ->
	     t:typ ->
	     ebody:exp ->
	     ht:epstep de de' ->
	     epstep (EFix (Some de) t ebody) (EFix (Some de') t ebody)
  | PsIf0E0 : e0:exp ->
              e0':exp ->
	      ethen:exp ->
	      eelse:exp ->
	      ht:epstep e0 e0' ->
	      epstep (EIf0 e0 ethen eelse) (EIf0 e0' ethen eelse)


type cfg =
  | Cfg : h:heap -> e:exp -> cfg

type eistep : cfg -> cfg -> Type =
  | IsRd : h:heap ->
            l:loc ->
            eistep (Cfg h (EApp (EConst EcBang) (EConst (EcLoc l)))) (Cfg h (h l))
  | IsWr : h:heap ->
            l:loc ->
            v:value ->
            eistep (Cfg h (EApp (EApp (EConst EcAssign) (EConst (EcLoc l))) v))
                   (Cfg (upd_heap l v h) (EConst EcUnit))
  | IsBeta :  h:heap ->
              t:typ ->
              ebody:exp ->
              v:value ->
              eistep (Cfg h (EApp (ELam t ebody) v)) (Cfg h (eesubst_beta v ebody))
  | IsFix : h:heap ->
            d:option exp ->
            t:typ -> 
	    ebody:exp ->
	    v:value ->
	    eistep (Cfg h (EApp (EFix d t ebody) v)) (Cfg h (eesubst_beta (EFix d t ebody) (eesubst_beta v ebody)))
            
  | IsIf0 :  h:heap ->
             e1:exp ->
             e2:exp ->
             eistep (Cfg h (EIf0 (EConst (EcInt 0)) e1 e2)) (Cfg h e1)
  | IsIfS : i:int{i<>0} ->
             e1:exp ->
             e2:exp ->
             eistep (Cfg h (EIf0 (EConst (EcInt i)) e1 e2)) (Cfg h e2)
  | IsAppE1 : h:heap ->
              e1:exp ->
              e1':exp ->
	      e2:exp ->
	      ht:epstep e1 e1' ->
	      eistep (Cfg h (EApp e1 e2)) (Cfg h (EApp e1' e2))
  | IsAppE2 : h:heap ->
              e1:exp ->
              e2:exp ->
	      e2':exp ->
	      ht:epstep e2 e2' ->
	      eistep (Cfg h (EApp e1 e2)) (Cfg h (EApp e1 e2'))
  | IsIf0E0 : h:heap ->
              e0:exp ->
              e0':exp ->
	      ethen:exp ->
	      eelse:exp ->
	      ht:epstep e0 e0' ->
	      eistep (Cfg h (EIf0 e0 ethen eelse)) (Cfg h (EIf0 e0' ethen eelse))

(********************************************************)
(* The signatures of Pure and ST and other Monad ops    *)
(********************************************************)
let k_pre_pure    = KType
let k_pre_all     = KTArr (TConst TcHeap) KType

let k_post_pure t = KTArr t KType
let k_post_all  t = KTArr t (KTArr (TConst TcHeap) KType)

let k_pure t      = KKArr (k_post_pure t) k_pre_pure
let k_all         = KKArr (k_post_all  t) k_pre_all

let tot t = Cmp CPure t (TTLam (post_pure t)
                               (TTApp (TTApp (TConst TcForall) t)
                                      (TELam t (TEApp (TVar 1) (EVar 0)))))
val return_pure : t:typ -> e:exp -> Tot typ
let return_pure t e = TTLam (k_post_pure t) (TEApp (TVar 0) e)

val return_all : t:typ -> e:exp -> Tot typ
let return_all t e = TTLam (k_post_all t) (TELam (TConst TcHeap) 
                    (TEApp (TEApp (TVar 0) e) (EVar 0)))
(*TODO: do not forget to shift up e !!!*)
(*Actually, can it have free variables ?*)
val bind_pure:  ta : typ -> tb : typ
             -> wp : typ
             -> f  : typ
             -> Tot typ
let bind_pure ta tb wp f = (* bind wp1 wp2 post = wp1 (fun (x:t1) -> wp2 x post) *)
(TTLam (k_post_pure tb) (*p*)
   TTApp (ttshift_up wp)
      (TELam (*shift*)(ttshift_up tb)(*x*)
         (TTApp (TEApp (ttshift_up (teshift_up f)) (TEVar 0)) (TVar 0))))
val bind_all:  ta:typ -> tb:typ 
             ->wp : typ
             ->f  : typ
             ->Tot typ
let bind_all ta tb wp f =
(TTLam (k_post_all tb) (*p*)
   TTApp (ttshift_up wp)
      (TELam (ttshift_up tb) (*x*)
         (TELam (TConst TcHeap) 
            (TEApp (TTApp (TEApp (ttshift_up (teshift_up (teshift_up f))) (EVar 1))
                          (TVar 0))
                   (EVar 0))))) 
(*
monotonic_M: #a:Type -> K_M(a) -> Type
monotonic_PURE a wp = forall p1 p2. (forall x. p1 x ==> p2 x) ==> (wp p1 ===> wp p2)
monotonic_ALL a wp = forall p1 p2. (forall x h. p1 x h ==> p2 x h) ==> (forall h. wp p1 h ===> wp p2 h)
*)
val monotonic_pure : a:typ -> wp:typ -> Tot typ
let monotonic_pure a wp =
tforallk (k_post_pure a)
(TTLam (k_post_pure a) 
  (tforallk (k_post_pure (tshift_up a))
    (TTLam (k_post_pure (tshift_up a))
      timpl 
      ((*forall x. p1 x ==> p2 x *)
        tforalle (tshift_up (tshift_up a))
         (TELam (tshift_up (tshift_up a)) 
           (timpl  (TEApp (TVar 1 (*p1*)) (EVar 0))
        	   (TEApp (TVar 0 (*p2*)) (EVar 0))
           ) 
         )
      )
      ((*wp p1 ==> wp p2*)
        timpl (TTApp (tshift_up (tshift_up wp)) (TVar 1))
              (TTApp (tshift_up (tshift_up wp)) (TVar 0))
      )
     )
   )
) 
(*
monotonic_ALL a wp = forall p1 p2. (forall x h. p1 x h ==> p2 x h) ==> (forall h. wp p1 h ===> wp p2 h)
*)
val monotonic_all : a:typ -> wp:typ -> Tot typ
let monotonic_all a wp =
tforallk (k_post_pure a)
(TTLam (k_post_pure a) 
  (tforallk (k_post_pure (tshift_up a))
    (TTLam (k_post_pure (tshift_up a))
      timpl 
      ((*forall x. p1 x ==> p2 x *)
        tforalle (tshift_up (tshift_up a))
         (TELam (tshift_up (tshift_up a)) 
           (tforalle (TConst TcHeap)
             (TELam (TConst TcHeap)
           	(timpl  (TEApp (TEApp (TVar 1 (*p1*)) (EVar 1(*x*))) (EVar 0) )
        	        (TEApp (TEApp (TVar 0 (*p2*)) (EVar 1)) (EVar 0))
           	) 
             )
           )
         )
      )
      ((*wp p1 ==> wp p2*)
        tforalle (TConst TcHeap)
        (TELam (TConst TcHeap)
          (timpl (TEApp (TTApp (tshift_up (tshift_up wp)) (TVar 1)) (EVar 0))
                 (TEApp (TTApp (tshift_up (tshift_up wp)) (TVar 0)) (EVar 0))
          )
        )
      )
    )
  )
) 
val op_pure : a:typ -> op:typ -> wp1:typ -> wp2:typ -> Tot typ
let op_pure op op1 op2 =
TTLam (k_post_pure a) (TTApp (TTApp (tshift_up op) (TTApp (tshift_up wp1) (TVar 0)))
                             (TTApp (tshift_up wp2) (TVar 0)))
val op_all : a:typ -> op:typ -> wp1:typ -> wp2:typ -> Tot typ
let op_all op op1 op2 =
TTLam (k_post_all a) 
  (TELam (TConst TcHeap)
    (TTApp (TTApp (teshift_up (tshift_up op)) (TEApp (TTApp (teshift_up (tshift_up wp1)) (TVar 0)) (EVar 0)))
           (TEApp (TTApp (teshift_up (tshift_up wp2)) (TVar 0)) (EVar 0)))
  )
val up_pure : a:typ -> t:typ -> Tot typ
let up_pure a wp =
TTLam (k_post_pure a) (tshift_up t)

val up_all : a:typ -> t:typ -> Tot typ
let up_all a wp =
TTLam (k_post_pure a) (TELam (TConst TcHeap) (teshift_up (tshift_up t)))

val down_pure : a:typ -> wp:typ -> Tot typ
let down_pure a wp =
(tforallk (k_post_pure a) (TTLam (k_post_pure a) (TTApp (tshift_up wp) (TVar 0)))) 

val down_all : a : typ -> wp:typ -> Tot typ
let down_all a wp =
(tforallk (k_post_all a) 
  (TTLam (k_post_all a) 
    (tforalle (TConst TcHeap)
      (TELam (TConst TcHeap)
        (
	 TEApp (TTApp (teshift_up (tshift_up wp)) (TVar 0)) (EVar 0)
	)
        
      )
    )
  )
)
val closee_pure : a:typ -> b:typ -> f:typ -> Tot typ
let closee_pure a b f =
(TTLam (k_post_pure a) (*p*)
 (tforalle (tshift_up b)
  (TELam (tshift_up b)
   (
    TTApp (TEApp (teshift_up (tshift_up f)) (EVar 0)) (TVar 0)
   )
  )

 )
)
val closee_all : a:typ -> b:typ -> f:typ -> Tot typ
let closee_all a b f =
(TTLam (k_post_all a) (*p*)
 (TELam (TConst TcHeap) (
   (tforalle (teshift_up (tshift_up b))
    (TELam (teshift_up (tshift_up b))
     (
      TEApp (TTApp (TEApp (teshift_up (teshift_up (tshift_up f))) (EVar 0)) (TVar 0)) (EVar 1)
     )
    )
   )
  )
 )
)
val closet_pure : a:typ -> f:typ -> Tot typ
let closet_pure a f =
(TTLam (k_post_pure a)
 (forallk KTyp
  (TTLam (KTyp) 
   (
    TTApp (TTApp (tshift_up (tshift_up f)) (TVar 0)) (TVar 1)
   )

  )
 )
)
val closet_all : a:typ -> f:typ -> Tot typ
let closet_all a f =
(TTLam (k_post_all a)
 (TELam (TConst TcHeap)
   (forallk KTyp
    (TTLam (KTyp) 
     (
      TEApp (TTApp (TTApp (tshift_up (teshift_up (tshift_up f))) (TVar 0)) (TVar 1)) (EVar 0)
     )

    )
   )
 )
)
(*
ite_M : #a:Type -> K_M(int) -> K_M(a) -> K_M(a) -> K_M(a)
ite_M a wp0 wp1 wp2 = bind_M wp0 (fun i -> (up_M (i  = 0) ==>_M wp1) /\_M
                                            (up_M (i != 0) ==>_M wp2))
*)
val ite_pure : a:typ -> wp0:typ -> wp1:typ -> wp2:typ -> Tot typ 
let ite_pure a wp0 wp1 wp2 =
bind_pure tint a wp0
(
 TELam (tint) 
  (
   tand 
    (
    )
    (
    )
  )
)
val lift_pure_st_wp : t:typ -> wp:typ -> Tot typ
let lift_pure_st_wp t wp =
  TTLam (* post *)
           (k_post_st t)
           (TELam (* h *)
              (TConst TcHeap)
              (TTApp (bump_typ 2 wp)
                 (TELam (* x *)
                    t
                    (TEApp (TEApp (TVar 2) (*post*) (EVar 0) (*x*)) (EVar 1)(*h*)))))

val lift_pure_st : c1:cmp{is_CPure (Cmp.m c1)}
                -> Tot cmp
let lift_pure_st (Cmp CPure t wp) =
  Cmp CSt t (lift_pure_st_wp t wp)

val bind_st:  c1:cmp{is_CSt (Cmp.m c1)}
           -> c2:cmp{is_CSt (Cmp.m c2)}
           -> Tot cmp
let bind_st (Cmp CSt t1 wp1) (Cmp CSt t2 wp2) =
  let wp2 = TELam t1 wp2 in
  Cmp CSt t2 (TTLam (* post *)
              (k_post_st t2)  (* don't need to bump t2, since we'll have a side condition ensuring that x:t1 not free in t2 *)
              (TTApp (bump_typ 1 wp1)
                 (TELam (* x *)
                    (bump_typ 1 t1)
                    (TTApp
                       (TEApp (bump_typ 2 wp2) (EVar 0))
                       (TVar 1)))))

val bind: c1:cmp -> c2:cmp -> Tot cmp
let bind c1 c2 = match c1, c2 with
  | Cmp CPure _ _, Cmp CPure _ _ -> bind_pure c1 c2
  | Cmp CSt _ _,   Cmp CSt _ _   -> bind_st   c1 c2
  | Cmp CSt _ _,   Cmp CPure _ _ -> bind_st   c1 (lift_pure_st c2)
  | Cmp CPure _ _, Cmp CSt _ _   -> bind_st   (lift_pure_st c1) c2

let conj phi1 phi2        = TTApp (TTApp (TConst TcAnd) phi1) phi2

(* AR: do we handle shifting up etc. here for phi ? *)
let close_forall t phi    = TTApp (TTApp (TConst TcForall) t) (TELam t phi)

let down_CPure t wp       = TTApp (TTApp (TConst TcForallPostPure) t)
                                  (TTLam (k_post_pure t) (TTApp (bump_typ 1 wp) (TVar 0)))
let down_CSt t wp         = TTApp (TTApp (TConst TcForallPostSt) t)
                                  (TTLam (k_post_st t)
                                     (TELam (TConst TcHeap) (TEApp (TTApp (bump_typ 2 wp) (TVar 1)) (EVar 0))))
let up_CPure t phi        = TTLam (k_post_pure t) (bump_typ 1 phi)
let up_CSt   t phi        = TTLam (k_post_st t)   (TELam (TConst TcHeap) (bump_typ 2 phi))
let op_CPure t op wp1 wp2 = TTLam (k_post_pure t) (TTApp (TTApp op
                                                            (TTApp (bump_typ 1 wp1) (TVar 0)))
                                                           (TTApp (bump_typ 1 wp2) (TVar 0)))
let op_CSt t op wp1 wp2   = TTLam (k_post_st t)   (TELam (TConst TcHeap) (TTApp (TTApp op
                                                                         (TEApp (TTApp (bump_typ 2 wp1) (TVar 1)) (EVar 0)))
                                                                  (TEApp (TTApp (bump_typ 2 wp2) (TVar 1)) (EVar 0))))

(* CH: unsure about this, especially its asymmetric nature (taking t2 discarding t1)
   NS [from review]: The (op op c1 c2) looks a bit fishy. Generally, the op functions have kind:
                a:Type -> M.WP a -> M.WP a -> M.WP a
      The result type is the same on both sides. Without it, you can’t apply the
      same post-condition to both of them.
let op op c1 c2 =
  match c1, c2 with
  | Cmp CPure _ wp1, Cmp CPure t2 wp2 -> Cmp CPure t2 (op_CPure t2 op wp1 wp2)
  | Cmp CPure _ wp1, Cmp CSt t2 wp2   -> Cmp CPure t2 (op_CSt t2 op (lift_pure_st_wp t2 wp1) wp2)
  | Cmp CSt _ wp1, Cmp CPure t2 wp2   -> Cmp CPure t2 (op_CSt t2 op wp1 (lift_pure_st_wp t2 wp2))
  | Cmp CSt _ wp1, Cmp CSt t2 wp2     -> Cmp CPure t2 (op_CSt t2 op wp1 wp2)
*)

let mk_eq t e1 e2      = TEApp (TEApp (TTApp (TConst TcEq) t) e1) e2
let neg phi            = TTApp (TConst TcNeg) phi

val bind_pure_if : exp -> c1:cmp{is_CPure (Cmp.m c1)} -> c2:cmp{is_CPure (Cmp.m c2)} -> Tot cmp
let bind_pure_if e (Cmp CPure t wp1) (Cmp CPure _ wp2) =
  let guard = mk_eq (TConst TcInt) e (EConst (EcInt 0)) in
  let wp = op_CPure t (TConst TcAnd) (op_CPure t (TConst TcImp) (up_CPure t guard) wp1) (op_CPure t (TConst TcImp) (up_CPure t (neg guard)) wp2) in
  Cmp CPure t wp

val bind_st_if : exp -> c1:cmp{is_CSt (Cmp.m c1)} -> c2:cmp{is_CSt (Cmp.m c2)} -> Tot cmp
let bind_st_if e (Cmp CSt t wp1) (Cmp CSt _ wp2) =
  let guard = mk_eq (TConst TcInt) e (EConst (EcInt 0)) in
  let wp = op_CSt t (TConst TcAnd) (op_CSt t (TConst TcImp) (up_CSt t guard) wp1) (op_CSt t (TConst TcImp) (up_CSt t (neg guard)) wp2) in
  Cmp CSt t wp

val bind_if : exp -> cmp -> cmp -> Tot cmp
let bind_if e c1 c2 = match c1, c2 with
  | Cmp CPure _ _, Cmp CPure _ _ -> bind_pure_if e c1 c2
  | Cmp CPure _ _, Cmp CSt _ _   -> bind_st_if e (lift_pure_st c1) c2
  | Cmp CSt _ _, Cmp CPure _ _   -> bind_st_if e c1 (lift_pure_st c2)
  | Cmp CSt _ _, Cmp CSt _ _     -> bind_st_if e c1 c2


(********************************************************)
(* Signature for constants                              *)
(********************************************************)

val tconsts : tconst -> Tot knd
let tconsts tc =
  match tc with
  | TcUnit
  | TcInt
  | TcRefInt
  | TcHeap
  | TcFalse
  | TcTrue   -> KType
                (* TODO: please double-check *)
  | TcAnd
  | TcOr
  | TcImpl    -> KKArr KType (KKArr KType KType)

  | TcForallE -> KKArr KType (KKArr (KTArr (TVar 0) KType) KType)

  | TcNeg    -> KKArr KType KType

  | TcEqE
  | TcPrecedes -> KKArr KType (KTArr (TVar 0) (KTArr (TVar 0) KType))
                 (* TODO: please double-check *)


val econsts : econst -> Tot typ
let econsts ec =
  match ec with
  | EcUnit   -> TConst TcUnit
  | EcInt _  -> TConst TcInt
  | EcLoc _  -> TConst TcRefInt
  | EcBang   -> TArr (TConst TcRefInt) (tot (TConst TcInt))
  | EcAssign -> TArr (TConst TcRefInt)
                     (tot (TArr (TConst TcInt)
                                (tot (TConst TcUnit))))
  | EcSel    -> TArr (TConst TcHeap)
                     (tot (TArr (TConst TcRefInt)
                                (tot (TConst TcInt))))
  | EcUpd    -> TArr (TConst TcHeap)
                     (tot (TArr (TConst TcRefInt)
                                (tot (TArr (TConst TcInt)
                                           (tot (TConst TcHeap))))))
