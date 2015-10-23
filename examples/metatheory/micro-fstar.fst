(*--build-config
    options:--z3timeout 20 --max_fuel 4 --max_ifuel 2 --initial_fuel 1 --initial_ifuel 1;
    other-files:classical.fst ext.fst constr.fst
  --*)
module MicroFStar

(* Formalization of micro-fstar proofs of progress and preservation
   for the PURE effect. The definitions cover most of micro-fstar, the
   only exceptions are 3 more recently introduced features:
   multi-monads, higher-order state, and dynamic
   allocation, however, none of these are relevant here, since our
   proofs are for the PURE effect. The proofs are mostly complete and
   all assumed lemmas are listed and explained below. Many are not yet
   complete because of limitations in our current F* implementation,
   which we hope to fix soon. *)

(*TODO list:

 definitions
 (void)

 substitution lemma
 * update VInjTH
 * write the substitution lemmas on type encodings (subst_on_bindall etc …)
   [F* limitations and take a lot of time to write, but easy things on paper]

 derived judgements
 * write the v_* validity derived judgements [take a lot of time to write]
 * write kdg_* to manipulate kinds with binding, wp etc …
   [F* limitations and take a lot of time to write]
 * finish validity_derived (V-Constr, VInjTH) [easy]
 * write kwf_* [take a lot of time to write]

 inversion lemmas (used in preservation and progress)
 * finish scmp_transitivity [need to write a validity proof term; difficult]
 * write stypingd_inversion_arrow [easy, same as styping_inversion_arrow]
 * correctly reorder styping inversion arrow lemmas, and write the bindings [easy]
 * code the case of application in value_inversion [long to write and difficult]
 * write inversion_tforalle / inversion_tforallt [long to write but easy]

 preservation lemma
 * write pure_to_tot [F* limitations and take long to write]
 * write the code for validity judgements [F* limitations]
 * write the PsFixPure case [F* limitation and hard to write]
 * write skdg_eqe and skdg_eqt [hard proofs that need a lot of rewriting]

 progress lemma
 * write tysub_derived [easy]
 * make the code compile without commenting some parts
   [F* limitations (I can not use split case here, as in other places)]
 * remove useless code (like tint_inversion_* )
 * write the bindings from already written code to *_empty
   (like styping_inversion_arrow_empty) [easy]

 optimization of verification
 * add split case option where useful
   * in substitution lemma, split_cases is mostly working but it is still
     not possible to add the full body of validity_substitution
 * update to finish with the adding of PsUpd, PsSel and PsFixPure
 * remove the useless rule about heap (since we added PsUpd and PsSel)

 other things to do
 * write section names at the end
 * remove useless code
*)


(*TODO in tiny-fstar.txt
 * simplify the proof of preservation:
   remove the useless preservation lemmas and do an induction on typing judgement
*)


open FStar.Classical
open FStar.FunctionalExtensionality
open FStar.Constructive

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
  | TELam : t:typ -> tbody:typ -> typ
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

(******************)
(* Free variables *)
(******************)

val eeappears : x:var -> e:exp -> Tot bool
(decreases %[e])
val teappears : x:var -> t:typ -> Tot bool
(decreases %[t])
val keappears : x:var -> k:knd -> Tot bool
(decreases %[k])
val eceappears : x:var -> ec:econst -> Tot bool
(decreases %[ec])
val tceappears : x:var -> tc:tconst -> Tot bool
(decreases %[tc])
val ceappears : x:var -> c:cmp -> Tot bool
(decreases %[c])

let rec eeappears x e =
match e with
| EVar y -> x = y
| EConst c -> eceappears x c
| ELam t ebody -> teappears x t || eeappears (x+1) ebody
| EIf0 eg et ee -> eeappears x eg || eeappears x et || eeappears x ee
| EApp e1 e2 -> eeappears x e1 || eeappears x e2
and teappears x t =
match t with
| TVar a -> false
| TConst c -> tceappears x c
| TArr t c -> teappears x t || ceappears (x+1) c
| TTLam k tbody -> keappears x k || teappears x tbody
| TELam t tbody -> teappears x t || teappears (x+1) tbody
| TTApp t1 t2 -> teappears x t1|| teappears x t2
| TEApp t e -> teappears x t || eeappears x e
and keappears x k =
match k with
| KType -> false
| KKArr karg kres -> keappears x karg || keappears x kres
| KTArr targ kres -> teappears x targ || keappears (x+1) kres
and eceappears x ec =
match ec with
| EcFixPure tx t' t'' wp -> teappears x tx || teappears x t' || teappears x t'' || teappears x wp
| EcFixOmega tx t' wp -> teappears x tx || teappears x t' || teappears x wp
| _ -> false
and tceappears x tc =
match tc with
| TcForallT k -> keappears x k
| TcEqT k -> keappears x k
| _ -> false
and ceappears x c =
let Cmp m t wp = c in teappears x t || teappears x wp

val is_value : exp -> Tot bool
let rec is_value e =
  match e with
  | EConst _
  | ELam _ _   -> true
  | EVar _
  | EIf0 _ _ _ -> false
  | EApp e1 e2 -> is_value e2 &&
      (match e1 with
       | EApp e11 e12 ->
         is_value e12 &&
         (match e11 with
          | EConst c -> (is_EcFixPure c || is_EcUpd c)
          | _ -> false)
       | EConst c -> (is_EcFixPure c || is_EcFixOmega c || is_EcUpd c || is_EcSel c || is_EcAssign c)
       | _ -> false)

type value = e:exp{is_value e}

let f e1 e2 = assert (is_value (EApp e1 e2) ==> is_value e1)

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
let tloc = TConst TcRefInt
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

let ttapp2 tf t1 t2 = TTApp (TTApp tf t1) t2
let tfalse = TConst TcFalse
let tand  a b = TTApp (TTApp (TConst TcAnd) a) b

let tforalle t p = TTApp (TTApp (TConst TcForallE) t) (TELam t p)
let tforallt k p = TTApp (TConst (TcForallT k)) (TTLam k p)

val teqe : typ -> exp -> exp -> Tot(typ)
let teqe t e1 e2 = TEApp (TEApp (TTApp (TConst TcEqE) t) e1) e2
(* SF : ^ TcEqE needs the type of the expression. To change *)
let teqt k t1 t2 = TTApp (TTApp (TConst (TcEqT k)) t1) t2
let teqtype = teqt KType

let tprecedes t1 t2 e1 e2 = TEApp (TEApp (ttapp2 (TConst TcPrecedes) t1 t2) e1) e2

let eapp2 efun earg1 earg2 = EApp (EApp efun earg1) earg2
let eapp3 efun earg1 earg2 earg3 = (EApp (EApp (EApp efun earg1) earg2) earg3)
(* SF : FIXME : problem here : bad kinding : TcPrecedes expect types *)

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

type erenaming (s:esub) = (forall (x:var). is_EVar (s x))

opaque val is_erenaming : s:esub -> GTot (n:int{(  erenaming s  ==> n=0) /\
                                                (~(erenaming s) ==> n=1)})
let is_erenaming s = (if excluded_middle (erenaming s) then 0 else 1)

type value_esub (s:esub) = (forall (x:var). is_value (s x))

val esub_id : esub
let esub_id = fun x -> EVar x

val esub_inc_gen : nat -> var -> Tot exp
let esub_inc_gen x y = EVar (y+x)

val esub_dec : var -> Tot exp
let esub_dec x = if x = 0 then EVar 0 else EVar (x-1)
(*
val esub_inc : var -> Tot exp
let esub_inc = esub_inc_gen 1
*)

val esub_inc : var -> Tot exp
let esub_inc x = EVar (x+1)

val esub_inc2 : var -> Tot exp
(* let esub_inc2 = esub_inc_gen 2 -- working around #311 *)
let esub_inc2 x = esub_inc_gen 2 x

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

val is_trenaming : s:tsub -> GTot (n:int{(  trenaming s  ==> n=0) /\
                                         (~(trenaming s) ==> n=1)})
let is_trenaming s = (if excluded_middle (trenaming s) then 0 else 1)

val tsub_inc_above : nat -> var -> Tot typ
let tsub_inc_above x y = if y<x then TVar y else TVar (y+1)
(*
val tsub_inc : var -> Tot typ
let tsub_inc = tsub_inc_above 0
*)

val tsub_inc : var -> Tot typ
let tsub_inc a = TVar (a+1)

val tsub_dec : var -> Tot typ
let tsub_dec x = if x = 0 then TVar 0 else TVar (x-1)

val tsub_id :tsub
let tsub_id = fun x -> TVar x


let is_tvar (t:typ) : int = if is_TVar t then 0 else 1

(********************************)
(* Global substitution function *)
(********************************)

(*The projectors for pairs were not working well with substitutions*)(*{{{*)
type sub =
| Sub : es:esub -> ts:tsub -> sub

opaque type renaming (s:sub) = (erenaming (Sub.es s))  /\ (trenaming (Sub.ts s))

opaque val is_renaming : s:sub -> GTot (n:int{(  renaming s  ==> n=0) /\
                                              (~(renaming s) ==> n=1)})
let is_renaming s = (if excluded_middle (renaming s) then 0 else 1)

type value_sub (s:sub) = (value_esub (Sub.es s))
type vsub = s:sub{value_sub s}

let sub_einc_gen y = Sub (esub_inc_gen y) tsub_id
(*
let sub_einc = sub_einc_gen 1
*)
let sub_einc = Sub esub_inc tsub_id
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
val sub_elam : s:sub -> Tot (r:sub{(renaming s ==> renaming r)})
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

val subst_on_value : s:sub -> e:exp -> Lemma (requires (is_value e)) (ensures (is_value (esubst s e)))
let rec subst_on_value s e =
admit()(*
match e with
| EConst _ -> ()
| ELam _ _ -> ()
| EVar _ -> ()
| EIf0 _ _ _ -> ()
| EApp e1 e2 -> (subst_on_value s e2;
    match e1 with
    | EApp e11 e12 -> (subst_on_value s e12;
      match e11 with
      | EApp (EConst EcUpd) e112 -> (subst_on_value s e112)
      | EConst c -> ()
      )
    | EConst c -> ()
    | _ -> ()
)
*)
(*
val elam_on_value_sub : s:sub -> Lemma (requires (value_sub s)) (ensures (value_sub (sub_elam s)))
let elam_on_value_sub s =
  let intro_lemma : (x:var -> Lemma (is_value (Sub.es (sub_elam s) x))) =
    fun x -> match x with
             | 0 -> ()
             | n -> (subst_on_value sub_einc ((Sub.es s) (x-1)))
  in
  forall_intro intro_lemma
val tlam_on_value_sub : s:sub -> Lemma (requires (value_sub s)) (ensures (value_sub (sub_tlam s)))
let tlam_on_value_sub s =
  let intro_lemma : (x:var -> Lemma (is_value (Sub.es (sub_tlam s) x))) =
    fun x -> (subst_on_value sub_tinc ((Sub.es s) (x)))
  in
  forall_intro intro_lemma
*)

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
(* let esub_ebeta = esub_ebeta_gen 0 -- working around #311 *)
let esub_ebeta e = esub_ebeta_gen 0 e

val sub_ebeta : exp -> Tot sub
let sub_ebeta e = Sub (esub_ebeta e) (tsub_id)

val esubst_ebeta : exp -> exp -> Tot exp
let esubst_ebeta e = esubst (sub_ebeta e)

val csubst_ebeta : exp -> cmp -> Tot cmp
let csubst_ebeta e = csubst (sub_ebeta e)

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
(* let tsub_tbeta = tsub_tbeta_gen 0 -- working around #311 *)
let tsub_tbeta t = tsub_tbeta_gen 0 t

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


val elam_on_sub_id : unit -> Lemma (sub_elam sub_id = sub_id)
let elam_on_sub_id x =
cut (FEq (Sub.es (sub_elam sub_id)) (Sub.es (sub_id)));
cut (FEq (Sub.ts (sub_elam sub_id)) (Sub.ts (sub_id)))

val tlam_on_sub_id : unit -> Lemma (sub_tlam sub_id = sub_id)
let tlam_on_sub_id x =
cut (FEq (Sub.es (sub_tlam sub_id)) (Sub.es (sub_id)));
cut (FEq (Sub.ts (sub_tlam sub_id)) (Sub.ts (sub_id)))


val esubst_with_sub_id : e:exp -> Lemma (esubst sub_id e = e)
val ecsubst_with_sub_id : ec:econst -> Lemma(ecsubst sub_id ec = ec)
val tsubst_with_sub_id : t:typ -> Lemma (tsubst sub_id t = t)
val tcsubst_with_sub_id : tc:tconst -> Lemma (tcsubst sub_id tc = tc)
val csubst_with_sub_id : c:cmp -> Lemma (csubst sub_id c = c)
val ksubst_with_sub_id : k:knd -> Lemma (ksubst sub_id k = k)

let rec esubst_with_sub_id e =
match e with
| EVar x -> ()
| EConst ec -> ecsubst_with_sub_id ec
| ELam t ebody -> (tsubst_with_sub_id t;
                   elam_on_sub_id ();
		   esubst_with_sub_id ebody)
| EIf0 g ethen eelse -> (
    esubst_with_sub_id g;
    esubst_with_sub_id ethen;
    esubst_with_sub_id eelse)
| EApp e1 e2 -> (
    esubst_with_sub_id e1;
    esubst_with_sub_id e2
    )
and ecsubst_with_sub_id ec =
match ec with
| EcFixPure tx t' t'' wp -> (
    tsubst_with_sub_id tx;
    tsubst_with_sub_id t';
    tsubst_with_sub_id t'';
    tsubst_with_sub_id wp
    )
| EcFixOmega tx t' wp -> (
    tsubst_with_sub_id tx;
    tsubst_with_sub_id t';
    tsubst_with_sub_id wp
    )
| _ -> ()
and tsubst_with_sub_id t =
match t with
| TVar a -> ()
| TConst tc -> tcsubst_with_sub_id tc
| TArr t c -> (
    tsubst_with_sub_id t;
    elam_on_sub_id ();
    csubst_with_sub_id c
    )
| TTLam k tbody -> (
    ksubst_with_sub_id k;
    tlam_on_sub_id ();
    tsubst_with_sub_id tbody
    )
| TELam t tbody -> (
    tsubst_with_sub_id t;
    elam_on_sub_id ();
    tsubst_with_sub_id tbody
    )
| TTApp t1 t2 -> (
    tsubst_with_sub_id t1;
    tsubst_with_sub_id t2
    )
| TEApp t e -> (
    tsubst_with_sub_id t;
    esubst_with_sub_id e
    )
and tcsubst_with_sub_id tc =
match tc with
| TcEqT k
| TcForallT k -> ksubst_with_sub_id k
| _ -> ()
and csubst_with_sub_id c =
let Cmp m t wp = c in
tsubst_with_sub_id t; tsubst_with_sub_id wp
and ksubst_with_sub_id k =
match k with
| KType -> ()
| KKArr k kbody -> (
    ksubst_with_sub_id k;
    tlam_on_sub_id ();
    ksubst_with_sub_id kbody
    )
| KTArr t kbody -> (
    tsubst_with_sub_id t;
    elam_on_sub_id ();
    ksubst_with_sub_id kbody
    )


(********************************)
(* Composition of substitutions *)
(********************************)

//{{{

val sub_comp : s1:sub -> s2:sub -> Tot sub
let sub_comp s1 s2 =
Sub (fun x -> esubst s1 (Sub.es s2 x)) (fun a -> tsubst s1 (Sub.ts s2 a))

val vsub_comp : s1:vsub -> s2:vsub -> Lemma (value_sub (sub_comp s1 s2))
let vsub_comp s1 s2 =
  let intro_lemma : x:var -> Lemma (is_value (Sub.es (sub_comp s1 s2) x)) = fun x ->
    subst_on_value s1 (Sub.es s2 x)
  in
  forall_intro intro_lemma

val sub_comp_einc1 : s:sub -> x:var -> Lemma (Sub.es (sub_comp sub_einc s) x = Sub.es (sub_comp (sub_elam s) sub_einc) x)
let sub_comp_einc1 s x = ()

val sub_comp_einc2 : s:sub -> x:var -> Lemma (Sub.ts (sub_comp sub_einc s) x = Sub.ts (sub_comp (sub_elam s) sub_einc) x)
let sub_comp_einc2 s x = ()

val sub_comp_einc : s:sub -> Lemma (sub_comp sub_einc s = sub_comp (sub_elam s) sub_einc)
let sub_comp_einc s =
  forall_intro (sub_comp_einc1 s);
  forall_intro (sub_comp_einc2 s);
  cut(FEq (Sub.es (sub_comp sub_einc s)) (Sub.es (sub_comp (sub_elam s) sub_einc)));
  cut(FEq (Sub.ts (sub_comp sub_einc s)) (Sub.ts (sub_comp (sub_elam s) sub_einc)))

val sub_comp_tinc1 : s:sub -> x:var -> Lemma (Sub.es (sub_comp sub_tinc s) x = Sub.es (sub_comp (sub_tlam s) sub_tinc) x)
let sub_comp_tinc1 s x = ()

val sub_comp_tinc2 : s:sub -> x:var -> Lemma (Sub.ts (sub_comp sub_tinc s) x = Sub.ts (sub_comp (sub_tlam s) sub_tinc) x)
let sub_comp_tinc2 s x = ()

val sub_comp_tinc : s:sub -> Lemma (sub_comp sub_tinc s = sub_comp (sub_tlam s) sub_tinc)
let sub_comp_tinc s =
  forall_intro (sub_comp_tinc1 s);
  forall_intro (sub_comp_tinc2 s);
  cut(FEq (Sub.es (sub_comp sub_tinc s)) (Sub.es (sub_comp (sub_tlam s) sub_tinc)));
  cut(FEq (Sub.ts (sub_comp sub_tinc s)) (Sub.ts (sub_comp (sub_tlam s) sub_tinc)))


#set-options "--split_cases 1"

val esubst_comp : s1:sub -> s2:sub -> e:exp -> Lemma (esubst s1 (esubst s2 e) = esubst (sub_comp s1 s2) e)
(decreases %[is_evar e; is_renaming s1; is_renaming s2; 1; e])
val ecsubst_comp : s1:sub -> s2:sub -> ec:econst -> Lemma (ecsubst s1 (ecsubst s2 ec) = ecsubst (sub_comp s1 s2) ec)
(decreases %[1; is_renaming s1; is_renaming s2; 1; ec])
val tsubst_comp : s1:sub -> s2:sub -> t:typ -> Lemma (tsubst s1 (tsubst s2 t) = tsubst (sub_comp s1 s2) t)
(decreases %[is_tvar t; is_renaming s1; is_renaming s2; 1; t])
val tcsubst_comp : s1:sub -> s2:sub -> tc:tconst -> Lemma (tcsubst s1 (tcsubst s2 tc) = tcsubst (sub_comp s1 s2) tc)
(decreases %[1; is_renaming s1; is_renaming s2; 1; tc])
val csubst_comp : s1:sub -> s2:sub -> c:cmp -> Lemma (csubst s1 (csubst s2 c) = csubst (sub_comp s1 s2) c)
(decreases %[1; is_renaming s1; is_renaming s2; 1; c])
val ksubst_comp : s1:sub -> s2:sub -> k:knd -> Lemma (ksubst s1 (ksubst s2 k) = ksubst (sub_comp s1 s2) k)
(decreases %[1; is_renaming s1; is_renaming s2; 1; k])
val sub_elam_comp : s1:sub -> s2:sub -> Lemma (sub_comp (sub_elam s1) (sub_elam s2) = sub_elam (sub_comp s1 s2))
(decreases %[1; is_renaming s1; is_renaming s2; 0; EVar 0])
val sub_tlam_comp : s1:sub -> s2:sub -> Lemma (sub_comp (sub_tlam s1) (sub_tlam s2) = sub_tlam (sub_comp s1 s2))
(decreases %[1; is_renaming s1; is_renaming s2; 0; TVar 0])

let rec esubst_comp s1 s2 e =
  match e with
| EVar x -> ()
| EConst ec -> ecsubst_comp s1 s2 ec
| ELam t ebody ->
(
 tsubst_comp s1 s2 t;
 esubst_comp (sub_elam s1) (sub_elam s2) ebody;
 sub_elam_comp s1 s2
)
| EIf0 eg et ee -> (esubst_comp s1 s2 eg; esubst_comp s1 s2 et; esubst_comp s1 s2 ee)
| EApp e1 e2 -> (esubst_comp s1 s2 e1; esubst_comp s1 s2 e2)
and ecsubst_comp s1 s2 ec = match ec with
| EcFixPure tx t' t'' wp -> (tsubst_comp s1 s2 tx; tsubst_comp s1 s2 t'; tsubst_comp s1 s2 t''; tsubst_comp s1 s2 wp)
| EcFixOmega tx t' wp -> (tsubst_comp s1 s2 tx; tsubst_comp s1 s2 t'; tsubst_comp s1 s2 wp)
| _ -> ()
and tsubst_comp s1 s2 t =
  match t with
| TVar x -> ()
| TConst tc -> tcsubst_comp s1 s2 tc
| TArr t c -> (
  tsubst_comp s1 s2 t;
  csubst_comp (sub_elam s1) (sub_elam s2) c;
  sub_elam_comp s1 s2
)
| TTLam k tbody -> (
    ksubst_comp s1 s2 k;
    tsubst_comp (sub_tlam s1) (sub_tlam s2) tbody;
    sub_tlam_comp s1 s2
)
| TELam t tbody -> (
    tsubst_comp s1 s2 t;
    tsubst_comp (sub_elam s1) (sub_elam s2) tbody;
    sub_elam_comp s1 s2
)
| TTApp t1 t2 -> (
    tsubst_comp s1 s2 t1;
    tsubst_comp s1 s2 t2
)
| TEApp t e -> (
    tsubst_comp s1 s2 t;
    esubst_comp s1 s2 e
)
and tcsubst_comp s1 s2 tc =
match tc with
| TcForallT k -> ksubst_comp s1 s2 k
| TcEqT k -> ksubst_comp s1 s2 k
| _ -> ()
and csubst_comp s1 s2 c =
let Cmp m t wp = c in
(
 tsubst_comp s1 s2 t;
 tsubst_comp s1 s2 wp
)
and ksubst_comp s1 s2 k =
  match k with
| KType -> ()
| KKArr karg kres -> (
    ksubst_comp s1 s2 karg;
    ksubst_comp (sub_tlam s1) (sub_tlam s2) kres;
    sub_tlam_comp s1 s2
)
| KTArr targ kres -> (
    tsubst_comp s1 s2 targ;
    ksubst_comp (sub_elam s1) (sub_elam s2) kres;
    sub_elam_comp s1 s2
)
and sub_elam_comp s1 s2 =
  let sub_elam_comp1 : x : var -> Lemma (Sub.es (sub_comp (sub_elam s1) (sub_elam s2)) x = Sub.es (sub_elam (sub_comp s1 s2)) x) = fun x -> match x with
  | 0 -> ()
  | n -> (
           (*esubst (sub_elam s1) (eesh (s2 (x-1))) *)
	   esubst_comp (sub_elam s1) sub_einc (Sub.es s2 (x-1));
	   (*esubst (sub_comp (sub_elam s1) sub_einc) (s2 (x-1)) *)
	   sub_comp_einc s1;
	   (*esubst (sub_comp sub_einc s1) (s2 (x-1))*)
	   esubst_comp sub_einc s1 (Sub.es s2 (x-1))
	   (*eesh (esubst (sub_comp s1 s2) (x-1)) = sub_elam (sub_comp s1 s2) x*)
         )
  in
  let sub_elam_comp2 : a : var -> Lemma (Sub.ts (sub_comp (sub_elam s1) (sub_elam s2)) a = Sub.ts (sub_elam (sub_comp s1 s2)) a) = fun a ->
     (*tsubst (sub_elam s1) (Sub.ts (sub_elam s2) a = tsubst (sub_elam s1) (tesh (s2 a))*)
      tsubst_comp (sub_elam s1) (sub_einc) (Sub.ts s2 a);
      sub_comp_einc s1;
      tsubst_comp sub_einc s1 (Sub.ts s2 a)
  in
  forall_intro sub_elam_comp1;
  forall_intro sub_elam_comp2;
  cut(FEq (Sub.es (sub_comp (sub_elam s1) (sub_elam s2))) (Sub.es (sub_elam (sub_comp s1 s2))));
  cut(FEq (Sub.ts (sub_comp (sub_elam s1) (sub_elam s2))) (Sub.ts (sub_elam (sub_comp s1 s2))))
and sub_tlam_comp s1 s2 =
  let sub_tlam_comp1 : a : var -> Lemma (Sub.ts (sub_comp (sub_tlam s1) (sub_tlam s2)) a = Sub.ts (sub_tlam (sub_comp s1 s2)) a) = fun a -> match a with
  | 0 -> ()
  | n -> (
	   tsubst_comp (sub_tlam s1) sub_tinc (Sub.ts s2 (a-1));
	   sub_comp_tinc s1;
	   tsubst_comp sub_tinc s1 (Sub.ts s2 (a-1))
         )
  in
  let sub_tlam_comp2 : x : var -> Lemma (Sub.es (sub_comp (sub_tlam s1) (sub_tlam s2)) x = Sub.es (sub_tlam (sub_comp s1 s2)) x) = fun x ->
     (*tsubst (sub_elam s1) (Sub.ts (sub_elam s2) a = tsubst (sub_elam s1) (tesh (s2 a))*)
      esubst_comp (sub_tlam s1) (sub_tinc) (Sub.es s2 x);
      sub_comp_tinc s1;
      esubst_comp sub_tinc s1 (Sub.es s2 x)
  in
  forall_intro sub_tlam_comp1;
  forall_intro sub_tlam_comp2;
  cut(FEq (Sub.es (sub_comp (sub_tlam s1) (sub_tlam s2))) (Sub.es (sub_tlam (sub_comp s1 s2))));
  cut(FEq (Sub.ts (sub_comp (sub_tlam s1) (sub_tlam s2))) (Sub.ts (sub_tlam (sub_comp s1 s2))))

#reset-options

type sub_equal (s1:sub) (s2:sub) = (FEq (Sub.es s1) (Sub.es s2) /\ FEq (Sub.ts s1) (Sub.ts s2) )
val sub_ext : s1:sub -> s2:sub{sub_equal s1 s2} -> Lemma(s1 = s2)
let sub_ext s1 s2 = ()

val edec_einc_comp : unit -> Lemma ((sub_comp sub_edec sub_einc) = sub_id)
let edec_einc_comp () = sub_ext (sub_comp sub_edec sub_einc) sub_id

val tdec_tinc_comp : unit -> Lemma ((sub_comp sub_tdec sub_tinc) = sub_id)
let tdec_tinc_comp () = sub_ext (sub_comp sub_tdec sub_tinc) sub_id

//}}}

(***********************************************)
(* Temporary zone to prove substitution lemmas *)
(***********************************************)

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

//{{{
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
              e:exp ->
              epstep (EApp (ELam t ebody) e) (esubst_ebeta e ebody)
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
  | PsFixPure : tx:typ -> t':typ -> t'':typ -> wp:typ ->
                d:exp -> f:exp -> v:value ->
                epstep (eapp3 (EConst (EcFixPure tx t' t'' wp)) d f v)
		       (eapp2 f v (eapp2 (EConst (EcFixPure tx t' t'' wp)) d f))
  | PsUpd : h:heap -> l:loc -> i:int ->
            epstep (eapp3 (EConst EcUpd) (eheap h) (eloc l) (eint i)) (eheap (upd_heap l i h))
  | PsSel : h:heap -> l:loc ->
            epstep (eapp2 (EConst EcSel) (eheap h) (eloc l)) (eint (h l))
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
//}}}

(********************************************************)
(* The signatures of Pure and ST and other Monad ops    *)
(********************************************************)
//{{{
let k_pre_pure    = KType
let k_pre_all     = KTArr theap KType

let k_post_pure t = KTArr t KType
let k_post_all  t = KTArr t (KTArr theap KType)

let k_pure t      = KKArr (k_post_pure t) k_pre_pure
let k_all  t      = KKArr (k_post_all  t) k_pre_all

let k_m m = match m with
| EfPure -> k_pure
| EfAll  -> k_all
let tot_wp t = (TTLam (k_post_pure t)
                           (tforalle (ttsh t) (TEApp (TVar 0) (EVar 0))))

let tot t = Cmp EfPure t (tot_wp t)
val return_pure : t:typ -> e:exp -> Tot typ
let return_pure t e = TTLam (k_post_pure t) (TEApp (TVar 0) (etsh e))

val return_pure_cmp : t:typ -> e:exp -> Tot cmp
let return_pure_cmp t e = Cmp EfPure t (return_pure t e)

let tot_wp_all t = (TTLam (k_post_all t)
                      (tforalle (ttsh t)
		          (tforalle (theap)
			      (TEApp (TEApp (TVar 0) (EVar 1)) (EVar 0)))))
let tot_all t = Cmp EfAll t (tot_wp_all t)

val return_all : t:typ -> e:exp -> Tot typ
let return_all t e = TTLam (k_post_all t) (TELam theap
                    (TEApp (TEApp (TVar 0) (eesh (etsh e))) (EVar 0)))

(*TODO: do not forget to shift up e !!!*)
(*Actually, can it have free variables ?*)
val bind_pure1:  ta : typ -> tb : typ
             -> wp : typ
             -> f  : typ
             -> Tot typ
let bind_pure1 ta tb wp f =
  TTApp (TEApp (tesh (ttsh f)) (EVar 0)) (TVar 0)
val bind_pure:  ta : typ -> tb : typ
             -> wp : typ
             -> f  : typ
             -> Tot typ
let bind_pure ta tb wp f =
   TTLam (k_post_pure tb) (*p*)
     (TTApp (ttsh wp)
        (TELam (*shift*)(ttsh tb)(*x*)
           (bind_pure1 ta tb wp f)))

let bind_all1 f =
(TEApp (TTApp (TEApp (tesh (tesh (ttsh f))) (EVar 1))
                            (TVar 0))
                     (EVar 0))
val bind_all:  ta:typ -> tb:typ
             ->wp : typ
             ->f  : typ
             ->Tot typ
let bind_all ta tb wp f =
  (TTLam (k_post_all tb) (*p*)
     (TTApp (ttsh wp)
        (TELam (ttsh tb) (*x*)
           (TELam theap
              (bind_all1 f)))))

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
           (teqe tint (EVar 0) (eint 0))
        )
         wp1
      )
      ((*up (i!=0) ==> wp2*)
       op_pure (tesh a) timpl
        (
         up_pure (tesh a)
           (tnot (teqe tint (EVar 0) (eint 0)))
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
           (teqe tint (EVar 0) (eint 0))
        )
         wp1
      )
      ((*up (i!=0) ==> wp2*)
       op_all (tesh a) timpl
        (
         up_all (tesh a)
           (tnot (teqe tint (EVar 0) (eint 0)))
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

(*val tfix_wp : tx:typ -> t'':typ -> d:exp -> wp:typ -> Tot typ
let tfix_wp tx t'' d wp =
  op_pure t'' tand
          (up_pure (t'') (TEApp (TEApp (TConst TcPrecedes) (EApp d (EVar 0)))
                                (EApp d (EVar 1)))) wp*)
(* SF : ^ to remove ? *)
val sub_computation : m:eff -> t:typ -> wp : typ -> m':eff{eff_sub m' m} -> t':typ -> w':typ -> Tot typ
let sub_computation m t wp m' t' wp' =
(down m t (op m t timpl wp (lift m' m t' wp')))

let tyapp_wp' t' wp e2 =
if teappears 0 t' then
tesh (tsubst (sub_ebeta e2) wp)
else
wp

let tyapp_wp m e2 t t' wp wp1 wp2 =
let tarr = (TArr t (Cmp m t' wp)) in
bind m tarr (tsubst (sub_ebeta e2) t') wp1
(TELam tarr (
	     tesh (bind m (t) (tsubst (sub_ebeta e2) t') (wp2)
	       (TELam (t) (tyapp_wp' t' wp e2)))
            )
)



let tconstr e t wp = tforallt (k_post_pure t) (timpl (TTApp (ttsh wp) (TVar 0)) (tand (ttsh t) (TEApp (TVar 0) (etsh e))))

//}}}

(********************************************************)
(* Signature for type and expression constants          *)
(********************************************************)

//{{{

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

let cmp_bang =
  Cmp EfAll tint (TTLam (k_post_all tint) (TELam theap
                   (TEApp (TEApp (TVar 0) (esel (EVar 0) (EVar 1))) (EVar 0))))

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
let tfixpuref tx t'' wp = TArr (teshg 2 tx) (Cmp EfPure (TEApp (teshg 3 t'') (EVar 0)) (op_pure (TEApp (teshg 3 t'') (EVar 0)) tand (up_pure (TEApp (teshg 3 t'') (EVar 0)) (tprecedes (TEApp (TVar 2) (EVar 0)) (TEApp (TVar 2) (EVar 1)) (EApp (EVar 2) (EVar 0)) (EApp (EVar 2) (EVar 1)))) (TEApp (teshg 3 wp) (EVar 0))))
let tfixpureF tx t'' wp = TArr (tesh tx) (tot (TArr (tfixpuref tx t'' wp) (Cmp EfPure (teshg 3 t'') (TEApp (teshg 3 wp) (EVar 1)))))
let tfixpuret tx t'' wp = TArr (teshg 2 tx) (Cmp EfPure (TEApp (teshg 3 t'') (EVar 0)) (TEApp (teshg 3 wp) (EVar 0)))
let tfixpure tx t' t'' wp = TArr (tfixpured tx t') (tot (TArr (tfixpureF tx t'' wp) (tot (tfixpuret tx t'' wp))))

let tfixomegatret tx t' wp = (Cmp EfAll (TEApp (teshg 2 t') (EVar 0)) (TEApp (teshg 2 wp) (EVar 0)))
let tfixomegat tx t' wp = TArr (tesh tx) (tfixomegatret tx t' wp)
let tfixomegaF tx t' wp = TArr (tx) (tot (TArr (tfixomegat tx t' wp) (Cmp EfAll (TEApp (teshg 2 t') (EVar 1)) (TEApp (teshg 2 wp) (EVar 1)))))
let tfixomega tx t' wp = TArr (tfixomegaF tx t' wp) (tot (tfixomegat tx t' wp))
val econsts : econst -> Tot typ
let econsts ec =
  match ec with
  | EcUnit   -> tunit
  | EcInt _  -> tint
  | EcLoc _  -> tref
  | EcBang   -> TArr tref (cmp_bang)
  | EcAssign -> TArr tref (tot (TArr tint (cmp_assign (EVar 1) (EVar 0))))
  | EcSel    -> TArr theap (tot (TArr tref (tot tint)))
  | EcUpd    -> TArr theap (tot (TArr tref (tot (TArr tint (tot theap)))))
  | EcHeap _ -> theap
  | EcFixPure tx t' t'' wp -> tfixpure tx t' t'' wp
  | EcFixOmega tx t' wp -> tfixomega tx t' wp


//}}}
(***********************)
(* Head normal forms   *)
(***********************)

//{{{
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
//}}}

(***********************)
(* Precedes on values  *)
(***********************)
//{{{
val precedes : v1:value -> v2:value -> Tot bool
let precedes v1 v2 =
  match v1, v2 with
  | EConst (EcInt i1), EConst (EcInt i2) -> i1 >= 0 && i2 >= 0 && i1 < i2
  | _, _ -> false
//}}}

(***********************)
(* Typing environments *)
(***********************)
//{{{
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
//}}}

(**************************)
(* Environment properties *)
(**************************)
//{{{
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
(*
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
  *)

(*SF: ^ normally useless now. but maybe used later …*)
//}}}
(**************)
(*   Typing   *)
(**************)
//{{{
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

| TyApp : #g:env -> #e1:exp -> #e2:exp -> #m:eff -> #t:typ ->
          #t':typ -> #wp:typ -> #wp1:typ -> #wp2:typ ->
          =ht1:typing g e1 (Cmp m (TArr t (Cmp m t' wp)) wp1) ->
	  =ht2:typing g e2 (Cmp m t wp2) ->
          =htot:option (typing g e2 (tot t)){teappears 0 t' ==> is_Some htot} ->
          =hk:option (kinding g (teshd t') KType){not (teappears 0 t') ==> is_Some hk} ->
	  typing g (EApp e1 e2) (Cmp m (tsubst (sub_ebeta e2) t') (tyapp_wp m e2 t t' wp wp1 wp2))

| TyRet : #g:env -> #e:exp -> t:typ ->
          typing g e (tot t) ->
          typing g e (Cmp EfPure t (return_pure t e))

| TySub : #g:env -> #e:exp -> #c':cmp -> #c:cmp ->
          =ht:typing g e c' ->
          =hsc:scmp g c' c ->
              typing g e c

and scmp : g:env -> c1:cmp -> c2:cmp -> Type =

| SCmp : #g:env -> m':eff -> #t':typ -> wp':typ ->
          m:eff{eff_sub m' m} -> #t:typ -> wp:typ ->
         =hs:styping g t' t ->
         =hk:kinding g wp (k_m m t) ->
         =hvmono:validity g (monotonic m t wp) ->
         =hk':kinding g wp' (k_m m' t') ->
         =hvmono':validity g (monotonic m' t' wp') ->
	 =hvsub :validity g (sub_computation m t wp m' t' wp') ->
             scmp g (Cmp m' t' wp') (Cmp m t wp)


and styping : g:env -> t':typ -> t:typ -> Type =
(*SF: a term styping does not tell us that t' is kind KType,
 but it should be ok since we can get that where it is used in TySub*)
| SubConv : #g:env -> #t:typ -> t':typ ->
            =hv:validity g (teqtype t' t) ->
            =hk:kinding g t KType ->
	    =hk':kinding g t' KType ->
                styping g t' t
(* SF : we could try to remove hk hk' at some point.
 But that would imply coding a more complicated derived lemma
 with a mutually recursive inversion for TTApp *)
| SubFun : #g:env -> #t:typ -> #t':typ ->
           #c':cmp -> #c:cmp ->
           =hst:styping g t t' ->
           =hsc:scmp (eextend t g) c' c ->
	   =hk':kinding g (TArr t' c') KType ->
                styping g (TArr t' c') (TArr t c)

| SubTrans : #g:env -> #t1:typ -> #t2:typ -> #t3:typ ->
             =hs12:styping g t1 t2 ->
             =hs23:styping g t2 t3 ->
                   styping g t1 t3
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

| KSub  : #g:env -> #t:typ -> #k':knd -> #k:knd ->
          =hk:kinding g t k' -> (* <- SF : can we not get it by derived judgement on hs ?*)
          =hs:skinding g k' k ->
              kinding g t k

and skinding : g:env -> k1:knd -> k2:knd -> Type=

| KSubRefl : #g:env -> #k:knd ->
             =hw:kwf g k ->
                 skinding g k k

| KSubKArr : #g:env -> #k1:knd -> #k2:knd -> k1':knd -> k2':knd ->
             =hs21 :skinding g k2 k1 ->
             =hs12':skinding (textend k2 g) k1' k2' ->
	     =hk:kwf g (KKArr k1 k1') ->
                    skinding g (KKArr k1 k1') (KKArr k2 k2')

| KSubTArr : #g:env -> #t1:typ -> #t2:typ -> #k1:knd -> #k2:knd ->
             =hs21:styping g t2 t1 ->
             =hs12':skinding (eextend t2 g) k1 k2 ->
	     =hk:kwf g (KTArr t1 k1) ->
                    skinding g (KTArr t1 k1) (KTArr t2 k2)

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

| VConstr : #g:env -> #e:exp -> #t:typ -> #wp:typ ->
            =h:typing g e (Cmp EfPure t wp) ->
               validity g (tconstr e t wp)

| VRedE   : #g:env -> #e:exp -> #t:typ -> #e':exp ->
            =ht :typing g e (tot t) ->
            =ht':typing g e' (tot t) ->
            =hst:epstep e e' ->
                 validity g (teqe t e e')

| VEqReflE : #g:env -> #e:exp -> #t:typ ->
             =ht:typing g e (tot t) ->
                 validity g (teqe t e e)

| VSubstE  : #g:env -> #e1:exp -> #e2:exp -> #t':typ -> t:typ ->
             =hv12 :validity g (teqe t' e1 e2) ->
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
                    validity g (teqe tint (esel (eheap h) (eloc l)) (eint (h l)))

| VUpdAsHeap : #g:env -> #h:heap -> #l:loc -> #i:int ->
               =hth:typing g (eheap h) (tot theap) ->
               =htl:typing g (eloc l) (tot tref) ->
               =hti:typing g (eint i) (tot tint) ->
                    validity g (teqe theap (eupd (eheap h) (eloc l) (eint i))
                                     (eheap (upd_heap l i h)))

| VSelEq : #g:env -> #eh:exp -> #el:exp -> #ei:exp ->
           =hth:typing g eh (tot theap) ->
           =htl:typing g el (tot tref) ->
           =hti:typing g ei (tot tint) ->
                validity g (teqe tint (esel (eupd eh el ei) el) ei)

| VSelNeq : #g:env -> #eh:exp -> #el:exp -> #el':exp -> #ei:exp ->
            =hth :typing g eh (tot theap) ->
            =htl :typing g el (tot tref) ->
            =htl':typing g el' (tot tref) ->
            =hti :typing g ei (tot tint) ->
            =hv  :validity g (tnot (teqe tloc el el')) ->
                  validity g (teqe tint (esel (eupd eh el' ei) ei) (esel eh el))

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
                        validity g (tprecedes t1 t2 v1 v2)

| VDistinctC : #g:env -> #t:typ -> #c1:econst -> #c2:econst{not (econst_eq c1 c2)} ->
               typing g (EConst c1) (tot t) ->
	       typing g (EConst c2) (tot t) ->
               validity g (tnot (teqe t (EConst c1) (EConst c2)))

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
               validity g (tand (tand (teqtype t1 t1') (tforalle t1 (teqtype t2 t2')))
                                      (tforalle t1 (teqt (k_m m t2) phi phi')))
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

//}}}
(****************************************)
(* Properties about usual substitutions *)
(****************************************)
//{{{
//NS: Writing 'requires' and 'ensures' will  give you better error messages

val esubst_elam_shift : s:sub -> e:exp -> Lemma (ensures (esubst (sub_elam s) (eesh e) = eesh (esubst s e)))
let esubst_elam_shift s e =
  esubst_comp (sub_elam s) sub_einc e;
  sub_comp_einc s;
  esubst_comp sub_einc s e

val tsubst_elam_shift : s:sub -> t:typ -> Lemma (ensures (tsubst (sub_elam s) (tesh t) = tesh (tsubst s t)))
let tsubst_elam_shift s t =
  tsubst_comp (sub_elam s) sub_einc t;
  sub_comp_einc s;
  tsubst_comp sub_einc s t

val ksubst_elam_shift : s:sub -> k:knd -> Lemma (ensures (ksubst (sub_elam s) (kesh k) = kesh (ksubst s k)))
let ksubst_elam_shift s k =
  ksubst_comp (sub_elam s) sub_einc k;
  sub_comp_einc s;
  ksubst_comp sub_einc s k

val esubst_tlam_shift : s:sub -> e:exp -> Lemma (esubst (sub_tlam s) (etsh e) = etsh (esubst s e))
let esubst_tlam_shift s e =
  esubst_comp (sub_tlam s) sub_tinc e;
  sub_comp_tinc s;
  esubst_comp sub_tinc s e

val tsubst_tlam_shift : s:sub -> t:typ -> Lemma (tsubst (sub_tlam s) (ttsh t) = ttsh (tsubst s t))
let tsubst_tlam_shift s t =
  tsubst_comp (sub_tlam s) sub_tinc t;
  sub_comp_tinc s;
  tsubst_comp sub_tinc s t

val ksubst_tlam_shift : s:sub -> k:knd -> Lemma (ksubst (sub_tlam s) (ktsh k) = ktsh (ksubst s k))
let ksubst_tlam_shift s k =
  ksubst_comp (sub_tlam s) sub_tinc k;
  sub_comp_tinc s;
  ksubst_comp sub_tinc s k

val tsubst_ebeta_elam_einc : t:typ -> Lemma (tsubst_ebeta (EVar 0) (tsubst (sub_elam sub_einc) t) = t)
let tsubst_ebeta_elam_einc t = admit()

val comp_ebeta_shift : e:exp -> Lemma (sub_comp (sub_ebeta e) (sub_einc) = sub_id)
let comp_ebeta_shift e =
cut(FEq (Sub.es (sub_comp (sub_ebeta e) (sub_einc))) (Sub.es (sub_id)));
cut(FEq (Sub.ts (sub_comp (sub_ebeta e) (sub_einc))) (Sub.ts (sub_id)))

val comp_tbeta_shift : t:typ -> Lemma (sub_comp (sub_tbeta t) (sub_tinc) = sub_id)
let comp_tbeta_shift t =
cut(FEq (Sub.es (sub_comp (sub_tbeta t) (sub_tinc))) (Sub.es (sub_id)));
cut(FEq (Sub.ts (sub_comp (sub_tbeta t) (sub_tinc))) (Sub.ts (sub_id)))


val esubst_ebeta_shift : e:exp -> ebody:exp -> Lemma (esubst (sub_ebeta e) (eesh ebody) = ebody)
let esubst_ebeta_shift e ebody =
esubst_comp (sub_ebeta e) (sub_einc) ebody;
comp_ebeta_shift e;
esubst_with_sub_id ebody

val tsubst_ebeta_shift : e:exp -> t:typ -> Lemma (tsubst (sub_ebeta e) (tesh t) = t)
let tsubst_ebeta_shift e t =
tsubst_comp (sub_ebeta e) (sub_einc) t;
comp_ebeta_shift e;
tsubst_with_sub_id t

val ksubst_ebeta_shift : e:exp -> k:knd -> Lemma (ksubst (sub_ebeta e) (kesh k) = k)
let ksubst_ebeta_shift e k =
ksubst_comp (sub_ebeta e) (sub_einc) k;
comp_ebeta_shift e;
ksubst_with_sub_id k

val esubst_tbeta_shift : t:typ -> e : exp -> Lemma (esubst (sub_tbeta t) (etsh e) = e)
let esubst_tbeta_shift t e =
esubst_comp (sub_tbeta t) (sub_tinc) e;
comp_tbeta_shift t;
esubst_with_sub_id e

val tsubst_tbeta_shift : t:typ -> tbody : typ -> Lemma (tsubst (sub_tbeta t) (ttsh tbody) = tbody)
let tsubst_tbeta_shift t tbody =
tsubst_comp (sub_tbeta t) (sub_tinc) tbody;
comp_tbeta_shift t;
tsubst_with_sub_id tbody

val ksubst_tbeta_shift : t:typ -> k : knd -> Lemma (ksubst (sub_tbeta t) (ktsh k) = k)
let ksubst_tbeta_shift t k =
ksubst_comp (sub_tbeta t) (sub_tinc) k;
comp_tbeta_shift t;
ksubst_with_sub_id k

val eeshd_eesh : e:exp -> Lemma (eeshd (eesh e) = e)
let eeshd_eesh e = admit()

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
//}}}
(***********************************)
(* Properties about free variables *)
(***********************************)
//{{{

val esubst_on_eappears : x:var -> s:sub{Sub.es s x = EVar x} -> e:exp ->
   Lemma (requires (eeappears x e)) (ensures (eeappears x (esubst s e)))
(decreases %[e])
val ecsubst_on_eappears : x:var -> s:sub{Sub.es s x = EVar x} -> ec:econst ->
   Lemma (requires (eceappears x ec)) (ensures (eceappears x (ecsubst s ec)))
(decreases %[ec])
val tsubst_on_eappears : x:var -> s:sub{Sub.es s x = EVar x} -> t:typ ->
   Lemma (requires (teappears x t)) (ensures (teappears x (tsubst s t)))
(decreases %[t])
val tcsubst_on_eappears : x:var -> s:sub{Sub.es s x = EVar x} -> tc:tconst ->
   Lemma (requires (tceappears x tc)) (ensures (tceappears x (tcsubst s tc)))
(decreases %[tc])
val csubst_on_eappears: x:var -> s:sub{Sub.es s x = EVar x} -> c:cmp ->
   Lemma (requires (ceappears x c)) (ensures (ceappears x (csubst s c)))
(decreases %[c])
val ksubst_on_eappears: x:var -> s:sub{Sub.es s x = EVar x} -> k:knd ->
   Lemma (requires (keappears x k)) (ensures (keappears x (ksubst s k)))
(decreases %[k])


let rec esubst_on_eappears x s e =
match e with
| EVar _ -> ()
| EConst c -> ecsubst_on_eappears x s c
| ELam t ebody -> if (teappears x t) then tsubst_on_eappears x s t
                  else esubst_on_eappears (x+1) (sub_elam s) ebody
| EIf0 eg et ee -> if (eeappears x eg) then esubst_on_eappears x s eg
                   else if (eeappears x et) then esubst_on_eappears x s et
		   else esubst_on_eappears x s ee
| EApp e1 e2 -> if (eeappears x e1) then esubst_on_eappears x s e1
                else esubst_on_eappears x s e2
and ecsubst_on_eappears x s ec =
match ec with
| EcFixPure tx t' t'' wp -> if teappears x tx then tsubst_on_eappears x s tx
                            else if teappears x t' then tsubst_on_eappears x s t'
			    else if teappears x t'' then tsubst_on_eappears x s t''
                            else tsubst_on_eappears x s wp
| EcFixOmega tx t' wp -> if teappears x tx then tsubst_on_eappears x s tx
                         else if teappears x t' then tsubst_on_eappears x s t'
  else tsubst_on_eappears x s wp
and tsubst_on_eappears x s t =
match t with
| TConst c -> tcsubst_on_eappears x s c
| TArr t c -> if teappears x t then tsubst_on_eappears x s t
              else csubst_on_eappears (x+1) (sub_elam s) c
| TTLam k tbody -> if keappears x k then ksubst_on_eappears x s k
                   else tsubst_on_eappears x (sub_tlam s) tbody
| TELam t tbody -> if teappears x t then tsubst_on_eappears x s t
                   else tsubst_on_eappears (x+1) (sub_elam s) tbody
| TTApp t1 t2 -> if teappears x t1 then tsubst_on_eappears x s t1
                 else tsubst_on_eappears x s t2
| TEApp t e -> if teappears x t then tsubst_on_eappears x s t
               else esubst_on_eappears x s e
and tcsubst_on_eappears x s tc =
match tc with
| TcForallT k -> ksubst_on_eappears x s k
| TcEqT k -> ksubst_on_eappears x s k
and csubst_on_eappears x s c =
let Cmp m t wp = c in
if teappears x t then tsubst_on_eappears x s t
else tsubst_on_eappears x s wp
and ksubst_on_eappears x s k =
match k with
| KKArr karg kres -> if keappears x karg then ksubst_on_eappears x s karg
                     else ksubst_on_eappears x (sub_tlam s) kres
| KTArr targ kres -> if teappears x targ then tsubst_on_eappears x s targ
                     else ksubst_on_eappears (x+1) (sub_elam s) kres

type sub_neappears : sub -> var -> var -> Type =
| SubEAppears : s:sub -> x:var -> y:var ->
                ef: (x':var{x<>x'} -> Lemma( not (eeappears y (Sub.es s x')))) ->
                tf: (a:var -> Lemma (not (teappears y (Sub.ts s a)))) ->
                sub_neappears s x y

opaque val einc_neappears : x:var -> Tot(sub_neappears sub_einc x (x+1))
let einc_neappears x =
SubEAppears sub_einc x (x+1)
  (fun x' -> ())
  (fun a -> ())

opaque val tinc_neappears : x:var -> Tot(sub_neappears sub_tinc x x)
let tinc_neappears x =
SubEAppears sub_tinc x x
  (fun x' -> ())
  (fun a -> ())

opaque val esubst_on_neappears : #s:sub -> #x:var -> #y:var ->
                          hs:sub_neappears s x y ->
                          e:exp ->
                          Pure unit (b2t (not (eeappears x e)))
                               (fun _ -> b2t (not (eeappears y (esubst s e))))
(decreases %[is_evar e; is_renaming s; 1; e])
opaque val ecsubst_on_neappears : #s:sub -> #x:var -> #y:var ->
                          hs:sub_neappears s x y ->
                          ec:econst ->
                          Pure unit (b2t (not (eceappears x ec)))
                               (fun _ -> b2t (not (eceappears y (ecsubst s ec))))
(decreases %[1; is_renaming s; 1; ec])
opaque val tsubst_on_neappears : #s:sub -> #x:var -> #y:var ->
                          hs:sub_neappears s x y ->
                          t:typ ->
                          Pure unit (b2t (not (teappears x t)))
                               (fun _ -> b2t (not (teappears y (tsubst s t))))
(decreases %[is_tvar t; is_renaming s; 1; t])
opaque val tcsubst_on_neappears : #s:sub -> #x:var -> #y:var ->
                          hs:sub_neappears s x y ->
                          tc:tconst ->
                          Pure unit (b2t (not (tceappears x tc)))
                               (fun _ -> b2t (not (tceappears y (tcsubst s tc))))
(decreases %[1; is_renaming s; 1; tc])
opaque val ksubst_on_neappears : #s:sub -> #x:var -> #y:var ->
                          hs:sub_neappears s x y ->
                          k:knd ->
                          Pure unit (b2t (not (keappears x k)))
                               (fun _ -> b2t (not (keappears y (ksubst s k))))
(decreases %[1; is_renaming s; 1; k])
opaque val csubst_on_neappears : #s:sub -> #x:var -> #y:var ->
                          hs:sub_neappears s x y ->
                          c:cmp ->
                          Pure unit (b2t (not (ceappears x c)))
                               (fun _ -> b2t (not (ceappears y (csubst s c))))
(decreases %[1; is_renaming s; 1; c])
opaque val elam_neappears : #s:sub -> #x:var -> #y:var ->
                     hs:sub_neappears s x y ->
		     Tot (sub_neappears (sub_elam s) (x+1) (y+1))
(decreases %[1; is_renaming s; 0; EVar 0])
opaque val tlam_neappears : #s:sub -> #x:var -> #y:var ->
                     hs:sub_neappears s x y ->
		     Tot (sub_neappears (sub_tlam s) x y)
(decreases %[1; is_renaming s; 0; TVar 0])

let rec esubst_on_neappears s x y hs e =
match e with
| EVar x -> SubEAppears.ef hs x
| EConst c -> ecsubst_on_neappears hs c
| ELam t ebody -> (tsubst_on_neappears hs t; esubst_on_neappears (elam_neappears hs) ebody)
| EIf0 eg et ee -> (esubst_on_neappears hs eg; esubst_on_neappears hs et; esubst_on_neappears hs ee)
| EApp e1 e2 -> (esubst_on_neappears hs e1; esubst_on_neappears hs e2)
and ecsubst_on_neappears s x y hs ec =
match ec with
| EcFixPure tx t' t'' wp -> (tsubst_on_neappears hs tx; tsubst_on_neappears hs t'; tsubst_on_neappears hs t''; tsubst_on_neappears hs wp)
| EcFixOmega tx t' wp -> (tsubst_on_neappears hs tx; tsubst_on_neappears hs t'; tsubst_on_neappears hs wp)
| _ -> ()
and tsubst_on_neappears s x y hs t =
match t with
| TVar a -> SubEAppears.tf hs a
| TConst c -> tcsubst_on_neappears hs c
| TArr t c -> (tsubst_on_neappears hs t; csubst_on_neappears (elam_neappears hs) c)
| TTLam k tbody -> (ksubst_on_neappears hs k; tsubst_on_neappears (tlam_neappears hs) tbody)
| TELam t tbody -> (tsubst_on_neappears hs t; tsubst_on_neappears (elam_neappears hs) tbody)
| TTApp t1 t2 -> (tsubst_on_neappears hs t1; tsubst_on_neappears hs t2)
| TEApp t e -> (tsubst_on_neappears hs t; esubst_on_neappears hs e)
and tcsubst_on_neappears s x y hs tc =
match tc with
| TcForallT k -> ksubst_on_neappears hs k
| TcEqT k -> ksubst_on_neappears hs k
| _ -> ()
and ksubst_on_neappears s x y hs k =
match k with
| KType -> ()
| KKArr karg kres -> (ksubst_on_neappears hs karg; ksubst_on_neappears (tlam_neappears hs) kres)
| KTArr targ kres -> (tsubst_on_neappears hs targ; ksubst_on_neappears (elam_neappears hs) kres)
and csubst_on_neappears s x y hs c =
let Cmp m t wp = c in
tsubst_on_neappears hs t; tsubst_on_neappears hs wp
and elam_neappears s x y hs =
let SubEAppears _ _ _ ef tf = hs in
SubEAppears (sub_elam s) (x+1) (y+1)
  (fun x' -> if x' = 0 then ()
             else (ef (x' - 1); esubst_on_neappears (einc_neappears y) (Sub.es s (x' - 1))))
  (fun a -> (tf a; tsubst_on_neappears (einc_neappears y) (Sub.ts s a)))
and tlam_neappears s x y hs =
let SubEAppears _ _ _ ef tf = hs in
SubEAppears (sub_tlam s) x y
  (fun x' -> ef x'; esubst_on_neappears (tinc_neappears y) (Sub.es s x'))
  (fun a -> if a = 0 then ()
            else (tf (a-1); tsubst_on_neappears (tinc_neappears y) (Sub.ts s (a-1))))

type sub_neappears_all : s:sub -> x:var -> Type =
| SubNEAppearsAll : s:sub -> x:var ->
              ef: (y:var -> Lemma (not (eeappears x (Sub.es s y)))) ->
	      tf: (a:var -> Lemma (not (teappears x (Sub.ts s a)))) ->
	      sub_neappears_all s x

(* added silly unit to work around #311 *)
opaque val einc_neappears_all : unit -> Tot (sub_neappears_all sub_einc 0)
let einc_neappears_all () =
  SubNEAppearsAll sub_einc 0
                  (fun y -> ())
                  (fun a -> ())

opaque val elam_on_neappears_all : #s:sub -> #x:var ->
             hs:sub_neappears_all s x ->
	     Tot (sub_neappears_all (sub_elam s) (x+1))
let elam_on_neappears_all s x hs =
SubNEAppearsAll (sub_elam s) (x+1)
(fun y -> match y with
  | 0 -> ()
  | n -> (SubNEAppearsAll.ef hs (n-1); esubst_on_neappears (einc_neappears x) (Sub.es s (n-1)))
)
(fun a -> (SubNEAppearsAll.tf hs a; tsubst_on_neappears (einc_neappears x) (Sub.ts s a))
)

opaque val tlam_on_neappears_all : #s:sub -> #x:var ->
             hs:sub_neappears_all s x ->
	     Tot (sub_neappears_all (sub_tlam s) x)
let tlam_on_neappears_all s x hs =
SubNEAppearsAll (sub_tlam s) (x)
(fun y -> (SubNEAppearsAll.ef hs y; esubst_on_neappears (tinc_neappears x) (Sub.es s y))
)
(fun a -> match a with
 | 0 -> ()
 | n -> (SubNEAppearsAll.tf hs (n-1); tsubst_on_neappears (tinc_neappears x) (Sub.ts s (n-1)))
)

val esubst_on_neappears_all : #s:sub -> #x:var ->
             hs:sub_neappears_all s x ->
	     e:exp ->
	     Lemma (not (eeappears x (esubst s e)))
(decreases %[e])
val ecsubst_on_neappears_all : #s:sub -> #x:var ->
             hs:sub_neappears_all s x ->
	     ec:econst ->
	     Lemma (not (eceappears x (ecsubst s ec)))
(decreases %[ec])
val tsubst_on_neappears_all : #s:sub -> #x:var ->
             hs:sub_neappears_all s x ->
	     t:typ ->
	     Lemma (not (teappears x (tsubst s t)))
(decreases %[t])
val tcsubst_on_neappears_all : #s:sub -> #x:var ->
             hs:sub_neappears_all s x ->
	     tc:tconst ->
	     Lemma (not (tceappears x (tcsubst s tc)))
(decreases %[tc])
val csubst_on_neappears_all : #s:sub -> #x:var ->
             hs:sub_neappears_all s x ->
	     c:cmp ->
	     Lemma (not (ceappears x (csubst s c)))
(decreases %[c])
val ksubst_on_neappears_all : #s:sub -> #x:var ->
             hs:sub_neappears_all s x ->
	     k:knd ->
	     Lemma (not (keappears x (ksubst s k)))
(decreases %[k])
(*val esubst_on … *)
(* SF : ^ essentially for elam_neappears0 at the moment *)
let rec esubst_on_neappears_all s x hs e =
match e with
| EVar x -> SubNEAppearsAll.ef hs x
| EConst ec -> ecsubst_on_neappears_all hs ec
| ELam t ebody -> (
    tsubst_on_neappears_all hs t;
    esubst_on_neappears_all (elam_on_neappears_all hs) ebody
    )
| EIf0 g ethen eelse -> (
    esubst_on_neappears_all hs g;
    esubst_on_neappears_all hs ethen;
    esubst_on_neappears_all hs eelse
    )
| EApp e1 e2 -> (
    esubst_on_neappears_all hs e1;
    esubst_on_neappears_all hs e2
    )
and ecsubst_on_neappears_all s x hs ec =
match ec with
| EcFixPure tx t' t'' wp -> (
    tsubst_on_neappears_all hs tx;
    tsubst_on_neappears_all hs t';
    tsubst_on_neappears_all hs t'';
    tsubst_on_neappears_all hs wp
    )
| EcFixOmega tx t' wp -> (
    tsubst_on_neappears_all hs tx;
    tsubst_on_neappears_all hs t';
    tsubst_on_neappears_all hs wp
    )
| _ -> ()
and tsubst_on_neappears_all s x hs t =
match t with
| TVar a -> SubNEAppearsAll.tf hs a
| TConst tc -> tcsubst_on_neappears_all hs tc
| TArr t c -> (
    tsubst_on_neappears_all hs t;
    csubst_on_neappears_all (elam_on_neappears_all hs) c
    )
| TTLam k tbody -> (
    ksubst_on_neappears_all hs k;
    tsubst_on_neappears_all (tlam_on_neappears_all hs) tbody
    )
| TELam t tbody -> (
    tsubst_on_neappears_all hs t;
    tsubst_on_neappears_all (elam_on_neappears_all hs) tbody
    )
| TTApp t1 t2 -> (
    tsubst_on_neappears_all hs t1;
    tsubst_on_neappears_all hs t2
    )
| TEApp t e -> (
    tsubst_on_neappears_all hs t;
    esubst_on_neappears_all hs e
    )
and tcsubst_on_neappears_all s x hs tc =
match tc with
| TcEqT k
| TcForallT k -> ksubst_on_neappears_all hs k
| _ -> ()
and csubst_on_neappears_all s x hs c =
let Cmp m t wp = c in
tsubst_on_neappears_all hs t;
tsubst_on_neappears_all hs wp
and ksubst_on_neappears_all s x hs k =
match k with
| KType -> ()
| KKArr karg kbody -> (
    ksubst_on_neappears_all hs karg;
    ksubst_on_neappears_all (tlam_on_neappears_all hs) kbody
    )
| KTArr targ kbody -> (
    tsubst_on_neappears_all hs targ;
    ksubst_on_neappears_all (elam_on_neappears_all hs) kbody
    )

type sub_almost_eq : s1:sub -> s2:sub -> x:var -> Type =
| SubAlmostEq : s1:sub -> s2:sub -> x:var ->
     ef: (y:var{y<>x} -> Lemma (Sub.es s1 y = Sub.es s2 y)) ->
     tf: (a:var -> Lemma (Sub.ts s1 a = Sub.ts s2 a)) ->
     sub_almost_eq s1 s2 x

opaque val elam_on_almost_eq : #s1:sub -> #s2:sub -> #x:var ->
          hs:sub_almost_eq s1 s2 x ->
	  Tot (sub_almost_eq (sub_elam s1) (sub_elam s2) (x+1))
let elam_on_almost_eq s1 s2 x hs =
SubAlmostEq (sub_elam s1) (sub_elam s2) (x+1)
(fun y -> match y with
  | 0 -> ()
  | n -> SubAlmostEq.ef hs (n-1)
)
(fun a -> SubAlmostEq.tf hs a)

opaque val tlam_on_almost_eq : #s1:sub -> #s2:sub -> #x:var ->
          hs:sub_almost_eq s1 s2 x ->
	  Tot (sub_almost_eq (sub_tlam s1) (sub_tlam s2) x)
let tlam_on_almost_eq s1 s2 x hs =
SubAlmostEq (sub_tlam s1) (sub_tlam s2) x
(fun y -> SubAlmostEq.ef hs y)
(fun a -> match a with
   | 0 -> ()
   | n -> SubAlmostEq.tf hs (n-1)
)

val esubst_with_almost_eq : #s1:sub -> #s2:sub -> #x:var ->
          hs:sub_almost_eq s1 s2 x ->
	  e:exp{not (eeappears x e)} ->
	  Lemma (esubst s1 e = esubst s2 e)
(decreases %[e])
val ecsubst_with_almost_eq : #s1:sub -> #s2:sub -> #x:var ->
          hs:sub_almost_eq s1 s2 x ->
	  ec:econst{not (eceappears x ec)} ->
	  Lemma (ecsubst s1 ec = ecsubst s2 ec)
(decreases %[ec])
val tsubst_with_almost_eq : #s1:sub -> #s2:sub -> #x:var ->
          hs:sub_almost_eq s1 s2 x ->
	  t:typ{not (teappears x t)} ->
	  Lemma (tsubst s1 t = tsubst s2 t)
(decreases %[t])
val tcsubst_with_almost_eq : #s1:sub -> #s2:sub -> #x:var ->
          hs:sub_almost_eq s1 s2 x ->
	  tc:tconst{not (tceappears x tc)} ->
	  Lemma (tcsubst s1 tc = tcsubst s2 tc)
(decreases %[tc])
val csubst_with_almost_eq : #s1:sub -> #s2:sub -> #x:var ->
          hs:sub_almost_eq s1 s2 x ->
	  c:cmp{not (ceappears x c)} ->
	  Lemma (csubst s1 c = csubst s2 c)
(decreases %[c])
val ksubst_with_almost_eq : #s1:sub -> #s2:sub -> #x:var ->
          hs:sub_almost_eq s1 s2 x ->
	  k:knd{not (keappears x k)} ->
	  Lemma (ksubst s1 k = ksubst s2 k)
(decreases %[k])
let rec esubst_with_almost_eq s2 s2 x hs e =
match e with
| EVar x -> SubAlmostEq.ef hs x
| EConst ec -> ecsubst_with_almost_eq hs ec
| ELam t ebody -> (
    tsubst_with_almost_eq hs t;
    esubst_with_almost_eq (elam_on_almost_eq hs) ebody
    )
| EIf0 g ethen eelse -> (
    esubst_with_almost_eq hs g;
    esubst_with_almost_eq hs ethen;
    esubst_with_almost_eq hs eelse
    )
| EApp e1 e2 -> (
    esubst_with_almost_eq hs e1;
    esubst_with_almost_eq hs e2
    )
and ecsubst_with_almost_eq s2 s2 x hs ec =
match ec with
| EcFixPure tx t' t'' wp -> (
    tsubst_with_almost_eq hs tx;
    tsubst_with_almost_eq hs t';
    tsubst_with_almost_eq hs t'';
    tsubst_with_almost_eq hs wp
    )
| EcFixOmega tx t' wp -> (
    tsubst_with_almost_eq hs tx;
    tsubst_with_almost_eq hs t';
    tsubst_with_almost_eq hs wp
    )
| _ -> ()
and tsubst_with_almost_eq s2 s2 x hs t =
match t with
| TVar a -> SubAlmostEq.tf hs a
| TConst tc -> tcsubst_with_almost_eq hs tc
| TArr t c -> (
    tsubst_with_almost_eq hs t;
    csubst_with_almost_eq (elam_on_almost_eq hs) c
    )
| TTLam k tbody ->(
    ksubst_with_almost_eq hs k;
    tsubst_with_almost_eq (tlam_on_almost_eq hs) tbody
    )
| TELam t tbody ->(
    tsubst_with_almost_eq hs t;
    tsubst_with_almost_eq (elam_on_almost_eq hs) tbody
    )
| TTApp t1 t2 ->(
    tsubst_with_almost_eq hs t1;
    tsubst_with_almost_eq hs t2
    )
| TEApp t e -> (
    tsubst_with_almost_eq hs t;
    esubst_with_almost_eq hs e
    )
and tcsubst_with_almost_eq s2 s2 x hs tc =
match tc with
| TcEqT k -> ksubst_with_almost_eq hs k
| TcForallT k -> ksubst_with_almost_eq hs k
| _ -> ()
and csubst_with_almost_eq s2 s2 x hs c =
let Cmp m t wp = c in
tsubst_with_almost_eq hs t; tsubst_with_almost_eq hs wp
and ksubst_with_almost_eq s2 s2 x hs k =
match k with
| KType -> ()
| KKArr k kbody -> (
    ksubst_with_almost_eq hs k;
    ksubst_with_almost_eq (tlam_on_almost_eq hs) kbody
    )
| KTArr t kbody -> (
    tsubst_with_almost_eq hs t;
    ksubst_with_almost_eq (elam_on_almost_eq hs) kbody
    )

opaque val edec_elam_almost_eq : s:sub -> Tot (sub_almost_eq (sub_comp s sub_edec) (sub_comp sub_edec (sub_elam s)) 0)
let edec_elam_almost_eq s =
SubAlmostEq (sub_comp s (sub_edec)) (sub_comp sub_edec (sub_elam s)) 0
     (fun y -> eeshd_eesh (Sub.es s (y-1)))
     (fun a -> (tsubst_comp sub_edec sub_einc (Sub.ts s a);
            edec_einc_comp ();
	    tsubst_with_sub_id (Sub.ts s a)))

opaque val edec_ebeta_almost_eq : e:exp -> Tot (sub_almost_eq (sub_edec) (sub_ebeta e) 0)
let edec_ebeta_almost_eq e =
SubAlmostEq sub_edec (sub_ebeta e) 0
     (fun y -> ())
     (fun a -> ())
(* SF : ^ for the TyApp case in typing_substitution for g |- teshd t' : Type *)

opaque val elam_neappears0 : s:sub -> Tot (sub_neappears (sub_elam s) 0 0)
let elam_neappears0 s =
SubEAppears (sub_elam s) 0 0
  (fun x -> esubst_on_neappears_all (einc_neappears_all ()) (Sub.es s (x-1)))
  (fun a -> tsubst_on_neappears_all (einc_neappears_all ()) (Sub.ts s a))

//}}}

(******************************************)
(* Lemmas about substitution on encodings *)
(******************************************)
//{{{

val subst_on_esel : s:sub -> eh:exp -> el:exp -> Lemma (esubst s (esel eh el) = esel (esubst s eh) (esubst s el))
let subst_on_esel s eh el = ()

val subst_on_cmp_bang : s:sub -> Lemma (csubst (sub_elam s) cmp_bang = cmp_bang)
let subst_on_cmp_bang s =
admit()(*
let Cmp EfAll _ wp = cmp_bang in
let wp1 = esel (EVar 0) (EVar 1) in
let wp2 = TEApp (TVar 0) wp1 in
let wp3 = TEApp wp2 (EVar 0) in
let wp4 = (TELam theap wp3) in
let wp5 = TTLam (k_post_all tint) wp4 in
let s1 = sub_elam s in
let s2 = sub_tlam (sub_elam s) in
let s3 = sub_elam (sub_tlam (sub_elam s)) in
let lemma1: unit -> Lemma (esubst s3 wp1 = wp1) = fun _ -> subst_on_esel s3 (EVar 0) (EVar 1) in
let lemma2: unit -> Lemma (tsubst s3 wp2 = wp2) = fun _ -> lemma1() in
let lemma3: unit -> Lemma (tsubst s3 wp3 = wp3) = fun _ -> lemma2() in
let lemma4: unit -> Lemma (tsubst s2 wp4 = wp4) = fun _ -> lemma3() in
let lemmaux : s:sub -> Lemma (ksubst s (k_post_all tint) = k_post_all tint) = fun s -> () in
let lemma5: unit -> Lemma (tsubst s1 wp5 = wp5) = fun _ -> lemma4(); lemmaux s1 in
let finallemma : unit -> Lemma( wp5 = wp ) = fun _ -> () in
(finallemma () ; lemma5())
*)



val subst_on_bind_pure1 : s:sub -> ta:typ -> tb:typ -> wp : typ -> f :typ -> Lemma (tsubst (sub_elam (sub_tlam s)) (bind_pure1 ta tb wp f) = bind_pure1 (tsubst s ta) (tsubst s tb) (tsubst s wp) (tsubst s f))
let subst_on_bind_pure1 s ta tb wp f =
admit()(*
  tsubst_elam_shift (sub_tlam s) (ttsh f);
  tsubst_tlam_shift s f
    *)
(* SF : fails sometimes *)
val subst_on_bind_pure : s:sub -> ta:typ -> tb:typ -> wp : typ -> f :typ -> Lemma (tsubst s (bind_pure ta tb wp f) = bind_pure (tsubst s ta) (tsubst s tb) (tsubst s wp) (tsubst s f))
let subst_on_bind_pure s ta tb wp f =
admit()(*
  tsubst_tlam_shift s wp;
  tsubst_tlam_shift s tb;
  subst_on_bind_pure1 s ta tb wp f
  *)

val subst_aux1 : s:sub -> t:typ -> Lemma (tsubst (sub_elam (sub_elam (sub_tlam s))) (tesh (tesh (ttsh t))) = tesh (tesh (ttsh (tsubst s t))))
let subst_aux1 s t = tsubst_elam_shift (sub_elam (sub_tlam s)) (tesh (ttsh t));
    tsubst_elam_shift (sub_tlam s) (ttsh t);
    tsubst_tlam_shift (s) (t)

val subst_on_bind_all1 : s:sub -> f :typ -> Lemma (tsubst (sub_elam (sub_elam (sub_tlam s))) (bind_all1 f) = bind_all1 (tsubst s f))
let subst_on_bind_all1 s f =
(*
  tsubst_elam_shift (sub_elam (sub_tlam s)) (tesh (ttsh f));
  tsubst_elam_shift (sub_tlam s) (ttsh f);
  tsubst_tlam_shift (s) (f)
*)
admit()(*
  let term1 = tesh (tesh (ttsh f)) in
  let term2 = TEApp term1 (EVar 1) in
  let term3 = TTApp term2 (TVar 0) in
  let term = TEApp term3 (EVar 0) in
  let term1' = tesh (tesh (ttsh (tsubst s f))) in
  let term2' = TEApp term1' (EVar 1) in
  let term3' = TTApp term2' (TVar 0) in
  let term' = TEApp term3' (EVar 0) in
  let s' = sub_elam (sub_elam (sub_tlam s)) in
  let lemma1: unit -> Lemma(tsubst s' (TVar 0) = TVar 0) = fun _ -> () in
  let lemma1':unit -> Lemma(esubst s' (EVar 1) = (EVar 1)) = fun _ -> () in
  let lemma2: unit -> Lemma(tsubst s' term1 = term1') = fun _ -> subst_aux1 s f in
  let lemma3: unit -> Lemma(tsubst s' term2 = term2') = fun _ -> lemma1'();lemma2 () in
  let lemma4: unit -> Lemma(tsubst s' term3 = term3') = fun _ -> lemma3() in
  let lemma5: unit -> Lemma(tsubst s' term = term') = fun _ -> lemma4() in
  lemma5()
*)
(*SF : FIXME*)
let bind_all1' f =
(TEApp (tesh (tesh (ttsh f))) (EVar 1))

val subst_on_bind_all1' : s:sub -> f :typ -> Lemma (tsubst (sub_elam (sub_elam (sub_tlam s))) (bind_all1' f) = bind_all1' (tsubst s f))
let subst_on_bind_all1' s f = admit()
(*
  tsubst_elam_shift (sub_elam (sub_tlam s)) (tesh (ttsh f));
  tsubst_elam_shift (sub_tlam s) (ttsh f);
  tsubst_tlam_shift (s) (f)
*)



val subst_on_k_post_all : s:sub -> t:typ ->
         Lemma(ksubst s (k_post_all t) = k_post_all (tsubst s t))
let subst_on_k_post_all s t = ()

val subst_on_bind_all : s:sub -> ta:typ -> tb:typ ->
                        wp:typ -> f:typ ->
                        Lemma(tsubst s (bind_all ta tb wp f) =
			     bind_all (tsubst s ta) (tsubst s tb) (tsubst s wp) (tsubst s f))
let subst_on_bind_all s ta tb wp f =
admit()(*
subst_on_k_post_all s tb;
tsubst_tlam_shift s wp;
tsubst_tlam_shift s tb;
subst_on_bind_all1 s f
*)


(* SF : ^ This proof is an ugly hack. And it is slow.
 Any idea to improve it ?*)

val subst_on_bind : s:sub -> m:eff -> tarr:typ -> t:typ -> wp1 : typ -> wp2 :typ -> Lemma (tsubst s (bind m tarr t wp1 wp2) = bind m (tsubst s tarr) (tsubst s t) (tsubst s wp1) (tsubst s wp2))
let subst_on_bind s m tarr t wp1 wp2 =
match m with
| EfPure -> subst_on_bind_pure s tarr t wp1 wp2
| EfAll -> subst_on_bind_all s tarr t wp1 wp2

val subst_on_ite_pure : s:sub -> a : typ -> wp0:typ -> wp1:typ -> wp2:typ ->
    Lemma(tsubst s (ite_pure a wp0 wp1 wp2) = ite_pure (tsubst s a) (tsubst s wp0) (tsubst s wp1) (tsubst s wp2))
let subst_on_ite_pure s a wp0 wp1 wp2 = admit()

val subst_on_ifi : s:sub -> i:int -> e1:exp -> e2:exp -> Lemma (esubst s (EIf0 (eint i) (e1) (e2)) = EIf0 (eint i) (esubst s e1) (esubst s e2))
let subst_on_ifi s i e1 e2 = ()
val subst_on_tforalle : s:sub -> t:typ -> body:typ -> Lemma (tsubst s (tforalle t body) = tforalle (tsubst s t) (tsubst (sub_elam s) body))
let subst_on_tforalle s t body = admit() (*works*)

val subst_on_tforallt : s:sub -> k:knd -> body:typ -> Lemma (tsubst s (tforallt k body) = tforallt (ksubst s k) (tsubst (sub_tlam s) body))
let subst_on_tforallt s k body = admit() (*works*)

val subst_on_tot : s:sub -> t:typ -> Lemma (csubst s (tot t) = tot (tsubst s t))
let subst_on_tot s t = subst_on_tforalle (sub_tlam s) (ttsh t) (TEApp (TVar 0) (EVar 0)); tsubst_tlam_shift s t; admit()(*works*)

val subst_on_return_pure : s:sub -> t:typ -> e:exp -> Lemma (tsubst s (return_pure t e) = return_pure (tsubst s t) (esubst s e))
let subst_on_return_pure s t e = esubst_tlam_shift s e; admit()(*works*)


val subst_on_teqtype : s:sub -> t:typ -> t':typ -> Lemma (tsubst s (teqtype t' t) = teqtype (tsubst s t') (tsubst s t))
let subst_on_teqtype s t t' = admit() (*works*)

(* CH: this needs lots of fuel to work *)
#set-options "--max_fuel 6 --initial_fuel 6"
val subst_on_teqe : s:sub -> t:typ -> e1:exp -> e2:exp -> Lemma (tsubst s (teqe t e1 e2) = teqe (tsubst s t) (esubst s e1) (esubst s e2))
let subst_on_teqe s t e1 e2 = ()
#reset-options

val subst_on_eupd : s:sub -> eh:exp -> el:exp -> ei:exp -> Lemma (esubst s (eupd (eh) (el) (ei)) = eupd (esubst s eh) (esubst s el) (esubst s ei))
let subst_on_eupd s eh el ei =
admit() (*works but slow*)

val subst_on_k_m : s:sub -> m:eff -> t:typ -> Lemma (ksubst s (k_m m t) = k_m m (tsubst s t))
let subst_on_k_m s m t =
admit()(* (*works but slow*)
  match m with
| EfPure -> ()
| EfAll -> ()
*)

val subst_on_teqt : s : sub -> k : knd -> t1:typ -> t2:typ -> Lemma (tsubst s (teqt k t1 t2) = teqt (ksubst s k) (tsubst s t1) (tsubst s t2))
let subst_on_teqt s k t1 t2 = ()

val sub_on_ebeta : s:sub -> e:exp -> Lemma (sub_comp s (sub_ebeta e) = sub_comp (sub_ebeta (esubst s e)) (sub_elam s))
let sub_on_ebeta s e =
let lemma1 : x:var -> Lemma (Sub.es (sub_comp s (sub_ebeta e)) x = Sub.es (sub_comp (sub_ebeta (esubst s e)) (sub_elam s)) x) = fun x ->
  if x = 0 then
    (* esubst s e = esubst s e *)
    ()
  else
    (* Sub.es s (x-1) = esubst (sub_ebeta (esubst s e)) (eesh (Sub.es s (x-1))) *)
  (
   esubst_ebeta_shift (esubst s e) (Sub.es s (x-1))
  )
in
let lemma2 : a:var -> Lemma (Sub.ts (sub_comp s (sub_ebeta e)) a = Sub.ts (sub_comp (sub_ebeta (esubst s e)) (sub_elam s)) a) = fun a ->
  (* Sub.ts s a = tsubst (sub_ebeta (esubst s e)) (tesh (Sub.ts s a)) *)
  tsubst_ebeta_shift (esubst s e) (Sub.ts s a)
in
forall_intro lemma1;
forall_intro lemma2;
cut(FEq (Sub.es (sub_comp s (sub_ebeta e))) (Sub.es (sub_comp (sub_ebeta (esubst s e)) (sub_elam s))));
cut(FEq (Sub.ts (sub_comp s (sub_ebeta e))) (Sub.ts (sub_comp (sub_ebeta (esubst s e)) (sub_elam s))))

val esubst_on_ebeta : s:sub -> e:exp -> ebody:exp -> Lemma (esubst s (esubst_ebeta e ebody) = esubst_ebeta (esubst s e) (esubst (sub_elam s) ebody))
let esubst_on_ebeta s e ebody =
esubst_comp (s) (sub_ebeta e) ebody;
sub_on_ebeta s e;
esubst_comp (sub_ebeta (esubst s e)) (sub_elam s) ebody

val tsubst_on_ebeta : s:sub -> e:exp -> t:typ -> Lemma (tsubst s (tsubst_ebeta e t) = tsubst_ebeta (esubst s e) (tsubst (sub_elam s) t))
let tsubst_on_ebeta s e t =
tsubst_comp (s) (sub_ebeta e) t;
sub_on_ebeta s e;
tsubst_comp (sub_ebeta (esubst s e)) (sub_elam s) t

val ksubst_on_ebeta : s:sub -> e:exp -> k:knd -> Lemma (ksubst s (ksubst_ebeta e k) = ksubst_ebeta (esubst s e) (ksubst (sub_elam s) k))
let ksubst_on_ebeta s e k =
ksubst_comp (s) (sub_ebeta e) k;
sub_on_ebeta s e;
ksubst_comp (sub_ebeta (esubst s e)) (sub_elam s) k

val sub_on_tbeta : s:sub -> t:typ -> Lemma (sub_comp s (sub_tbeta t) = sub_comp (sub_tbeta (tsubst s t)) (sub_tlam s))
let sub_on_tbeta s t =
let lemma1 : x:var -> Lemma (Sub.es (sub_comp s (sub_tbeta t)) x = Sub.es (sub_comp (sub_tbeta (tsubst s t)) (sub_tlam s)) x) = fun x ->
  (
   esubst_tbeta_shift (tsubst s t) (Sub.es s x)
  )
in
let lemma2 : a:var -> Lemma (Sub.ts (sub_comp s (sub_tbeta t)) a = Sub.ts (sub_comp (sub_tbeta (tsubst s t)) (sub_tlam s)) a) = fun a ->
  (* Sub.ts s a = tsubst (sub_ebeta (esubst s e)) (tesh (Sub.ts s a)) *)
  if a = 0 then ()
  else tsubst_tbeta_shift (tsubst s t) (Sub.ts s (a-1))
in
forall_intro lemma1;
forall_intro lemma2;
cut(FEq (Sub.es (sub_comp s (sub_tbeta t))) (Sub.es (sub_comp (sub_tbeta (tsubst s t)) (sub_tlam s))));
cut(FEq (Sub.ts (sub_comp s (sub_tbeta t))) (Sub.ts (sub_comp (sub_tbeta (tsubst s t)) (sub_tlam s))))

val tsubst_on_tbeta : s:sub -> t:typ -> tbody : typ -> Lemma (tsubst s (tsubst_tbeta t tbody) = tsubst_tbeta (tsubst s t) (tsubst (sub_tlam s) tbody))
let tsubst_on_tbeta s t tbody =
tsubst_comp (s) (sub_tbeta t) tbody;
sub_on_tbeta s t;
tsubst_comp (sub_tbeta (tsubst s t)) (sub_tlam s) tbody

val ksubst_on_tbeta : s:sub -> t:typ -> k:knd -> Lemma (ksubst s (ksubst_tbeta t k) = ksubst_tbeta (tsubst s t) (ksubst (sub_tlam s) k))
let ksubst_on_tbeta s t k =
ksubst_comp (s) (sub_tbeta t) k;
sub_on_tbeta s t;
ksubst_comp (sub_tbeta (tsubst s t)) (sub_tlam s) k



val subst_on_ite : s:sub -> m : eff -> t:typ -> wp0:typ -> wp1:typ -> wp2:typ ->
Lemma (tsubst s (ite m t wp0 wp1 wp2) = ite m (tsubst s t) (tsubst s wp0) (tsubst s wp1) (tsubst s wp2))
let subst_on_ite s m t wp0 wp1 wp2 = admit()

val subst_on_sub_computation : s:sub -> m:eff -> t:typ -> wp:typ -> m':eff{eff_sub m' m} -> t':typ -> wp':typ -> Lemma (tsubst s (sub_computation m t wp m' t' wp') = sub_computation  m (tsubst s t) (tsubst s wp) m' (tsubst s t') (tsubst s wp'))
let subst_on_sub_computation s m t wp m' t' wp' = admit()



val subst_on_monotonic : s:sub -> m:eff -> t:typ -> wp:typ -> Lemma (tsubst s (monotonic m t wp) = monotonic m (tsubst s t) (tsubst s wp))
let subst_on_monotonic s m t wp = admit()


val subst_on_teconst : s:sub -> ec:econst -> Lemma (tsubst s (econsts ec) = econsts (ecsubst s ec))
let subst_on_teconst s ec =
match ec with
| EcUnit -> ()
| EcInt _ -> ()
| EcLoc _ -> ()
| EcBang -> subst_on_cmp_bang s
| _ -> admit()

val subst_on_tconst : s:sub -> tc:tconst -> Lemma (tconsts (tcsubst s tc) = ksubst s (tconsts tc))
let subst_on_tconst s tc = admit()

val subst_on_tand : s:sub -> a:typ -> b:typ -> Lemma (tsubst s (tand a b) = tand (tsubst s a) (tsubst s b))
let subst_on_tand s a b = admit()

val subst_on_tor : s:sub -> t1 : typ -> t2 : typ -> Lemma (tsubst s (tor t1 t2) = tor (tsubst s t1) (tsubst s t2))
let subst_on_tor s t1 t2 = admit()

val subst_on_tnot : s:sub -> t:typ -> Lemma (tsubst s (tnot t) = tnot (tsubst s t))
let subst_on_tnot s t = admit()


val subst_on_ktarrow : s:sub -> t:typ -> k:knd -> Lemma (ksubst s (KTArr t k) = KTArr (tsubst s t) (ksubst (sub_elam s) k))
let subst_on_ktarrow s t k = ()
val subst_on_tarrow : s:sub -> t1:typ -> m:eff -> t2:typ -> wp:typ ->
Lemma (tsubst s (TArr t1 (Cmp m t2 wp)) = TArr (tsubst s t1) (Cmp m (tsubst (sub_elam s) t2) (tsubst (sub_elam s) wp)))
let subst_on_tarrow s t1 m t2 wp = admit()

val subst_on_elam : s:sub -> t1:typ -> ebody : exp ->
Lemma (esubst s (ELam t1 ebody) = ELam (tsubst s t1) (esubst (sub_elam s) ebody))
let subst_on_elam s t1 ebody = admit()


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


val tyif01 : s:sub -> e0:exp -> e1:exp -> e2:exp -> Lemma (esubst s (EIf0 e0 e1 e2) = EIf0 (esubst s e0) (esubst s e1) (esubst s e2))
let tyif01 s e0 e1 e2 = ()
val tyif02 : s:sub -> m:eff -> wp0:typ -> Lemma(csubst s (Cmp m tint wp0) = Cmp m tint (tsubst s wp0))
let tyif02 s m wp0 = ()
val tyif03 : s:sub -> m:eff -> t:typ -> wp:typ -> Lemma (csubst s (Cmp m t wp) = Cmp m (tsubst s t) (tsubst s wp))
let tyif03 s m t wp = ()
(* SF : ^ old naming. need to change it *)

val subst_on_op_timpl : s:sub -> m:eff -> t:typ -> wp1:typ -> wp2:typ ->
   Lemma (tsubst s (op m t timpl wp1 wp2) = op m (tsubst s t) timpl (tsubst s wp1) (tsubst s wp2))
let subst_on_op_timpl s m t wp1 wp2 = admit()

val subst_on_tyapp_wp : s:sub -> m:eff -> e2:exp -> t:typ ->
                        t':typ -> wp:typ -> wp1:typ -> wp2:typ ->
			Lemma (tsubst s (tyapp_wp m e2 t t' wp wp1 wp2) = tyapp_wp m (esubst s e2) (tsubst s t) (tsubst (sub_elam s) t') (tsubst (sub_elam s) wp) (tsubst s wp1) (tsubst s wp2))
let subst_on_tyapp_wp s m e2 t t' wp wp1 wp2 = admit()

val subst_on_tconstr : s:sub -> e:exp -> t:typ -> wp:typ ->
    Lemma (tsubst s (tconstr e t wp) = tconstr (esubst s e) (tsubst s t) (tsubst s wp))
let subst_on_tconstr s e t wp = admit()

val subst_on_tprecedes : s:sub -> t1:typ -> t2:typ -> e1:exp -> e2:exp ->
  Lemma (tsubst s (tprecedes t1 t2 e1 e2) = tprecedes (tsubst s t1) (tsubst s t2) (esubst s e1) (esubst s e2))
let subst_on_tprecedes s t1 t2 e1 e2 = admit()


//}}}

(***************************************************)
(* Substitution on reduction of pure exp and types *)
(***************************************************)
//{{{

(* CH: this needs lots of fuel to work *)
#set-options "--max_fuel 6 --initial_fuel 6"

opaque val epstep_substitution : s:sub -> e:exp -> e':exp -> hs:epstep e e' -> Tot (epstep (esubst s e) (esubst s e'))
(decreases %[hs])
opaque val tstep_substitution : s:sub -> t:typ -> t':typ -> hs:tstep t t' -> Tot (tstep (tsubst s t) (tsubst s t'))
(decreases %[hs])
let rec epstep_substitution s e e' hs =
match hs with
| PsBeta t ebody e ->
(
    let hr : epstep (EApp (ELam (tsubst s t) (esubst (sub_elam s) ebody)) (esubst s e)) (esubst_ebeta (esubst s e) (esubst (sub_elam s) ebody)) = PsBeta (tsubst s t) (esubst (sub_elam s) ebody) (esubst s e) in
    esubst_on_ebeta s e ebody;
    hr
    )
| PsIf0 e1 e2 -> PsIf0 (esubst s e1) (esubst s e2)
| PsIfS i e1 e2 -> (subst_on_ifi s i e1 e2;PsIfS i (esubst s e1) (esubst s e2))
| PsAppE1 #e1 #e1' e2 ht -> PsAppE1 (esubst s e2) (epstep_substitution s e1 e1' ht)
| PsAppE2 e1 #e2 #e2' ht -> PsAppE2 (esubst s e1) (epstep_substitution s e2 e2' ht)
| PsLamT #t #t' ebody ht -> (
    let htg2 : tstep (tsubst s t) (tsubst s t') = tstep_substitution s t t' ht in
    PsLamT (esubst (sub_elam s) ebody) htg2
    )
| PsIf0E0 #e0 #e0' ethen eelse ht -> let htg2 : epstep (esubst s e0) (esubst s e0') = epstep_substitution s e0 e0' ht in PsIf0E0 (esubst s ethen) (esubst s eelse) htg2
| PsFixPure tx t' t'' wp d f v ->
(
 magic()(*
 subst_on_value s v;
 PsFixPure (tsubst s tx) (tsubst s t') (tsubst s t'') (tsubst s wp) (esubst s d) (esubst s f) (esubst s v)
 *)
 (*SF : this is long …*)
)
| PsUpd h l i -> hs
| PsSel h l -> hs
and tstep_substitution s t t' hs =
match hs with
| TsEBeta tx t e -> (
    let hr : tstep (TEApp (TELam (tsubst s tx) (tsubst (sub_elam s) t)) (esubst s e)) (tsubst_ebeta (esubst s e) (tsubst (sub_elam s) t)) = TsEBeta (tsubst s tx) (tsubst (sub_elam s) t) (esubst s e) in
    tsubst_on_ebeta s e t;
    hr
    )
| TsTBeta k t t' ->
(
   let hr:tstep (TTApp (TTLam (ksubst s k) (tsubst (sub_tlam s) t)) (tsubst s t')) (tsubst_tbeta (tsubst s t') (tsubst (sub_tlam s) t)) = TsTBeta (ksubst s k) (tsubst (sub_tlam s) t) (tsubst s t') in
   tsubst_on_tbeta s t' t;
   hr
)
| TsArrT1 #t1 #t1' c ht -> (
    let hr: tstep (tsubst s t1) (tsubst s t1') = tstep_substitution s t1 t1' ht in
    TsArrT1 #(tsubst s t1) #(tsubst s t1') (csubst (sub_elam s) c) hr
)
| TsTAppT1 #t1 #t1' t2 ht -> (
    let hr : tstep (tsubst s t1) (tsubst s t1') = tstep_substitution s t1 t1' ht in
    TsTAppT1 #(tsubst s t1) #(tsubst s t1') (tsubst s t2) hr
    )
| TsTAppT2 t1 #t2 #t2' ht ->
(
 let hr : tstep (tsubst s t2) (tsubst s t2') = tstep_substitution s t2 t2' ht in
 TsTAppT2 (tsubst s t1) #(tsubst s t2) #(tsubst s t2') hr
)
| TsEAppT #t #t' e ht ->
(
 let hr : tstep (tsubst s t) (tsubst s t') = tstep_substitution s t t' ht in
 TsEAppT #(tsubst s t) #(tsubst s t') (esubst s e) hr
)
| TsEAppE t #e #e' he ->
(
 let hr : epstep (esubst s e) (esubst s e') = epstep_substitution s e e' he in
 TsEAppE (tsubst s t) #(esubst s e) #(esubst s e') hr
)
| TsTLamT k #t #t' ht ->
(
 let hr :tstep (tsubst (sub_tlam s) t) (tsubst (sub_tlam s) t') = tstep_substitution (sub_tlam s) t t' ht in
 TsTLamT (ksubst s k) #(tsubst (sub_tlam s) t) #(tsubst (sub_tlam s) t') hr
)
| TsELamT1 #t1 #t1' t2 ht -> (
    let hr : tstep (tsubst s t1) (tsubst s t1') = tstep_substitution s t1 t1' ht in
    TsELamT1 #(tsubst s t1) #(tsubst s t1') (tsubst (sub_elam s) t2) hr
    )

#reset-options

//}}}

(*********************************)
(* Substitution Arrow Definition *)
(*********************************)

//{{{

type subst_typing : s:sub -> g1:env -> g2:env -> Type =
| SubstTyping : s:sub-> g1:env -> g2:env ->
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

(* CH: can't make this opaque or SMT will loop forever! *)
val is_renaming_typing : #s:sub -> #g1:env -> #g2:env -> hs:subst_typing s g1 g2 -> Tot (r:nat{is_RenamingTyping hs ==> r = 0 /\ is_SubstTyping hs ==> r = 1})
let is_renaming_typing s g1 g2 hs = if (is_RenamingTyping hs) then 0 else 1

//}}}

(*****************************)
(* Usual Substitution Arrows *)
(*****************************)
//{{{
opaque val hs_sub_einc : g:env -> t:typ ->
Tot(r:subst_typing sub_einc g (eextend t g){is_RenamingTyping r})
let hs_sub_einc g t =
      let temp : subst_typing sub_einc g (eextend t g) = RenamingTyping sub_einc g (eextend t g)
		  (fun x ->  TyVar (x+1)
		  )
		  (fun a -> KVar a )
		  in temp
opaque val hs_sub_tinc : g:env -> k:knd ->
           Tot(r:subst_typing sub_tinc g (textend k g){is_RenamingTyping r})
let hs_sub_tinc g k =
      RenamingTyping sub_tinc g (textend k g)
		  (fun x ->  TyVar x) (fun a -> KVar (a+1))

opaque val hs_sub_id : g:env -> Tot (r:subst_typing sub_id g g{is_RenamingTyping r})
let hs_sub_id g =
RenamingTyping sub_id g g (fun x -> tsubst_with_sub_id (Some.v (lookup_evar g x)); TyVar x) (fun a -> ksubst_with_sub_id (Some.v (lookup_tvar g a)); KVar a)

opaque val ebeta_hs : #g:env -> #e:exp -> #t:typ ->
               ht:typing g e (tot t) ->
	       Tot (subst_typing (sub_ebeta e) (eextend t g) g)
let ebeta_hs g e t ht =
SubstTyping (sub_ebeta e) (eextend t g) g
(fun x -> match x with
       | 0 -> (tsubst_ebeta_shift e t; ht)
       | _ -> (tsubst_ebeta_shift e (Some.v (lookup_evar g (x-1))); TyVar (x-1))
)
(fun a -> (ksubst_ebeta_shift e (Some.v (lookup_tvar g a)); KVar a))

opaque val tbeta_hs : #g:env -> #t:typ -> #k:knd ->
               hk:kinding g t k ->
	       Tot (subst_typing (sub_tbeta t) (textend k g) g)
let tbeta_hs g t k hk =
SubstTyping (sub_tbeta t) (textend k g) g
(fun x -> tsubst_tbeta_shift t (Some.v (lookup_evar g x)); TyVar x)
(fun a -> match a with
       | 0 -> (ksubst_tbeta_shift t k; hk)

       | _ -> (ksubst_tbeta_shift t (Some.v (lookup_tvar g (a-1))); KVar (a-1))
)

(*
opaque val compose_with_renaming_arrow : g1 : env -> g2 : env -> g3 : env -> s12 : sub -> s23 : sub -> hs12 : subst_typing s12 g1 g2{ is_RenamingTyping hs12} -> hs23 : subst_typing s23 g2 g3 -> Tot (hr : subst_typing (sub_comp s23 s12) g1 g3)
let compose_with_renaming_arrow g1 g2 g3 s12 s23 hs12 hs23 =
let RenamingTyping _ _ _ ef12 tf12 = hs12 in
match hs23 with
| RenamingTyping _ _ _ ef23 tf23 ->
(
RenamingTyping (sub_comp s23 s12) g1 g3
(fun x -> let TyVar x' = ef12 x in ef23 x')
(fun a -> let KVar a' = tf12 a in tf23 a')
)
| SubstTyping _ _ _ ef23 tf23 ->
(
SubstTyping (sub_comp s23 s12) g1 g3
(fun x -> let TyVar x' = ef12 x in ef23 x')
(fun a -> let KVar a' = tf12 a in tf23 a')
)
(*SF : ^ FIXME, even though this function is useless*)
*)

//}}}

(**********************)
(* Substitution Lemma *)
(**********************)

//{{{

val is_tyvar : #g:env -> #e:exp -> #t:cmp -> ht:typing g e t -> Tot nat
let is_tyvar g e t ht = if is_TyVar ht then 0 else 1

val is_kvar : #g : env -> #t:typ -> #k:knd -> hk : kinding g t k -> Tot nat
let is_kvar g t k hk = if is_KVar hk then 0 else 1

(* CH: this doesn't always help, on the the contrary
#set-options "--split_cases 1" *)

(* CH: seems not needed on my machine, but needed on Markulf's Surface *)
#set-options "--z3timeout 20"

opaque val typing_substitution : #g1:env -> #e:exp -> #c:cmp -> s:sub -> #g2:env ->
    h1:typing g1 e c ->
    hs:subst_typing s g1 g2 ->
    Tot (hr:typing g2 (esubst s e) (csubst s c) {is_RenamingTyping hs /\ is_TyVar h1 ==> is_TyVar hr} )
(decreases %[is_tyvar h1; is_renaming_typing hs; 1;h1])
opaque val scmp_substitution : #g1:env -> #c1:cmp -> #c2:cmp -> s:sub -> #g2:env ->
    h1:scmp g1 c1 c2 ->
    hs:subst_typing s g1 g2 ->
    Tot (scmp g2 (csubst s c1) (csubst s c2) )
(decreases %[1; is_renaming_typing hs; 1; h1])
opaque val styping_substitution : #g1:env -> #t':typ -> #t:typ -> s:sub -> #g2:env ->
    h1:styping g1 t' t ->
    hs:subst_typing s g1 g2 ->
    Tot (styping g2 (tsubst s t') (tsubst s t) )
(decreases %[1;is_renaming_typing hs; 1; h1])
opaque val tcwf_substitution : #g1:env -> #c:tconst -> s:sub -> #g2:env ->
                        h1:tcwf g1 c ->
			hs:subst_typing s g1 g2 ->
			Tot (tcwf g2 (tcsubst s c))
(decreases %[1;is_renaming_typing hs; 1; h1])
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
opaque val skinding_substitution : #g1:env -> #k1:knd -> #k2:knd -> s:sub -> #g2:env ->
    h1:skinding g1 k1 k2 ->
    hs:subst_typing s g1 g2 ->
    Tot (skinding g2 (ksubst s k1) (ksubst s k2) )
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
(*SF : ^ it is still not possible to test all validity_substitution at once.
 Try the proof for each case with '~>' *)
opaque val elam_hs : #g1:env -> s:sub -> #g2:env -> t:typ ->
                         hs:subst_typing s g1 g2 ->
                         Tot (hr:subst_typing (sub_elam s) (eextend t g1) (eextend (tsubst s t) g2){is_RenamingTyping hs ==> is_RenamingTyping hr})
(decreases %[1;is_renaming_typing hs; 0; EVar 0])
opaque val tlam_hs : #g1:env -> s:sub -> #g2:env -> k:knd ->
                         hs:subst_typing s g1 g2 ->
                         Tot (hr:subst_typing (sub_tlam s) (textend k g1) (textend (ksubst s k) g2){is_RenamingTyping hs ==> is_RenamingTyping hr})
(decreases %[1;is_renaming_typing hs; 0; TVar 0])
let rec typing_substitution g1 e c s g2 h1 hs = magic()
(* CH: this started failing 2015-08-26, but was very flaky before too
match h1 with
| TyVar #g1 x ->
( match hs with
| SubstTyping _ _ _ ef tf -> (subst_on_tot s (Cmp.t c); ef x)
| RenamingTyping _ _ _ ef tf -> (subst_on_tot s (Cmp.t c); ef x)
)
| TyConst g ec hw ->
    (
     let hwg2 : ecwf g2 (ecsubst s ec) = ecwf_substitution s hw hs in
     subst_on_tot s (econsts ec);
     subst_on_teconst s ec;
     TyConst g2 (ecsubst s ec) hwg2 )
| TyIf0 g e0 e1 e2 m t wp0 wp1 wp2 he0 he1 he2 ->
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
| TyApp #g #e1 #e2 #m #t #t' #wp #wp1 #wp2 ht1 ht2 htot hk ->
(
let ht1g2 : typing g2 (esubst s e1) (Cmp m (TArr (tsubst s t) (Cmp m (tsubst (sub_elam s) t') (tsubst (sub_elam s) wp))) (tsubst s wp1)) =
subst_on_tarrow s t m t' wp; typing_substitution #g1 #e1 #(Cmp m (TArr t (Cmp m t' wp)) wp1) s #g2 ht1 hs in
let ht2g2 : typing g2 (esubst s e2)  (Cmp m (tsubst s t) (tsubst s wp2)) = typing_substitution #g1 #e2 #(Cmp m t wp2) s #g2 ht2 hs in
if (teappears 0 t') then
(
  tsubst_on_eappears 0 (sub_elam s) t';
  let htotg2 : ht: option(typing g2 (esubst s e2) (tot (tsubst s t))){is_Some ht} = subst_on_tot s t; let Some htotv = htot in Some (typing_substitution #g1 #e2 #(tot t) s #g2 htotv hs) in
  let happg2 : typing g2 (EApp (esubst s e1) (esubst s e2)) (Cmp m (tsubst s (tsubst_ebeta e2 t')) (tsubst s (tyapp_wp m e2 t t' wp wp1 wp2))) = subst_on_tyapp_wp s m e2 t t' wp wp1 wp2; tsubst_on_ebeta s e2 t'; subst_on_bind s m (TArr t (Cmp m t' wp)) t wp1 wp2; TyApp #g2 #(esubst s e1) #(esubst s e2) #m #(tsubst s t) #(tsubst (sub_elam s) t') #(tsubst (sub_elam s) wp) #(tsubst s wp1) #(tsubst s wp2) ht1g2 ht2g2 (htotg2) None in
  happg2
)
else
(
  tsubst_on_neappears (elam_neappears0 s) t';
  let hkg2 : hk:(option (kinding g2 (teshd (tsubst (sub_elam s) t')) KType)){is_Some hk} = let temp : kinding g2 (teshd (tsubst (sub_elam s) t')) KType = tsubst_with_almost_eq (edec_elam_almost_eq s) t'; tsubst_comp s sub_edec t'; tsubst_comp sub_edec (sub_elam s) t'; kinding_substitution s (Some.v hk) hs in Some temp in
  let happg2 : typing g2 (EApp (esubst s e1) (esubst s e2)) (Cmp m (tsubst s (tsubst_ebeta e2 t')) (tsubst s (tyapp_wp m e2 t t' wp wp1 wp2))) = subst_on_tyapp_wp s m e2 t t' wp wp1 wp2; tsubst_on_ebeta s e2 t'; subst_on_bind s m (TArr t (Cmp m t' wp)) t wp1 wp2; TyApp #g2 #(esubst s e1) #(esubst s e2) #m #(tsubst s t) #(tsubst (sub_elam s) t') #(tsubst (sub_elam s) wp) #(tsubst s wp1) #(tsubst s wp2) ht1g2 ht2g2 None hkg2 in
  happg2
)
)
| TyRet t ht ->
let htg2 : typing g2 (esubst s e) (tot (tsubst s t))=subst_on_tot s t; typing_substitution s ht hs in
let hretg2 : typing g2 (esubst s e) (Cmp EfPure (tsubst s t) (tsubst s (return_pure t e))) = subst_on_return_pure s t e; TyRet (tsubst s t) htg2 in
hretg2
| TySub #g #e #c' #c ht hsc ->
(
let htg2 : typing g2 (esubst s e) (csubst s c') = typing_substitution s ht hs in
let hscg2 : scmp g2 (csubst s c') (csubst s c) = scmp_substitution s hsc hs in
TySub htg2 hscg2
)
 *)
and scmp_substitution g1 c1 c2 s g2 h1 hs =
let SCmp #g m' #t' wp' m #t wp hsub hk hvmono hk' hvmono' hvsub = h1 in
let hsubg2 = styping_substitution s hsub hs in
let hkg2 : kinding g2 (tsubst s wp) (k_m m (tsubst s t)) = subst_on_k_m s m t; kinding_substitution s hk hs in
let hvmonog2 : validity g2 (monotonic m (tsubst s t) (tsubst s wp)) = subst_on_monotonic s m t wp; validity_substitution s hvmono hs in
let hk'g2 : kinding g2 (tsubst s wp') (k_m m' (tsubst s t')) = subst_on_k_m s m' t'; kinding_substitution s hk' hs in
let hvmono'g2 : validity g2 (monotonic m' (tsubst s t') (tsubst s wp')) = subst_on_monotonic s m' t' wp'; validity_substitution s hvmono' hs in
let hvsubg2 : validity g2 (sub_computation m (tsubst s t) (tsubst s wp) m' (tsubst s t') (tsubst s wp')) = subst_on_sub_computation s m t wp m' t' wp'; validity_substitution s hvsub hs in
let hscmpg2 : scmp g2 (Cmp m' (tsubst s t') (tsubst s wp')) (Cmp m (tsubst s t) (tsubst s wp))  = SCmp m' (tsubst s wp') m (tsubst s wp) hsubg2 hkg2 hvmonog2 hk'g2 hvmono'g2 hvsubg2 in
hscmpg2
and styping_substitution g1 t' t s g2 h1 hs =
match h1 with
| SubConv #g #t t' hv hk hk' ->
let hvg2 : validity g2 (teqtype (tsubst s t') (tsubst s t)) = subst_on_teqtype s t t'; validity_substitution s hv hs in
let hkg2 : kinding g2 (tsubst s t) KType = kinding_substitution s hk hs in
let hk'g2 : kinding g2 (tsubst s t') KType = kinding_substitution s hk' hs in
let hsubg2 : styping g2 (tsubst s t') (tsubst s t) = SubConv (tsubst s t') hvg2 hkg2 hk'g2 in hsubg2
| SubFun #g #t #t' #c' #c hst hsc hk' ->
(
let hstg2 : styping g2 (tsubst s t) (tsubst s t') = styping_substitution s hst hs in
let hscg2 : scmp (eextend (tsubst s t) g2) (csubst (sub_elam s) c') (csubst (sub_elam s) c) = scmp_substitution (sub_elam s) hsc (elam_hs s t hs) in
let hk'g2 : kinding g2 (tsubst s (TArr t' c')) KType = kinding_substitution s hk' hs in
let hr : styping g2 (TArr (tsubst s t') (csubst (sub_elam s) c')) (TArr (tsubst s t) (csubst (sub_elam s) c))  = SubFun hstg2 hscg2 hk'g2 in
hr
)
| SubTrans #g #t1 #t2 #t3 hs12 hs23 ->
SubTrans (styping_substitution s hs12 hs) (styping_substitution s hs23 hs)
and tcwf_substitution g1 c s g2 h1 hs =
match h1 with
|WFTcForallT #g #k hkw ->
WFTcForallT (kwf_substitution s hkw hs)
|WFTcEqT #g #k hkw ->
WFTcEqT (kwf_substitution s hkw hs)
|WFTcOther g tc ->
WFTcOther g2 tc
and ecwf_substitution g1 ec s g2 h1 hs =
match h1 with
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
and kinding_substitution g1 t k s g2 h1 hs =
match h1 with
| KVar #g x ->
(
match hs with
| SubstTyping _ _ _ _ tf -> tf x
| RenamingTyping _ _ _ _ tf -> tf x
)
| KConst #g #c htc ->
subst_on_tconst s c; KConst #g2 #(tcsubst s c) (tcwf_substitution s htc hs)
| KArr #g #t1 #t2 #phi #m hk1 hk2 hkp hv ->
let hsext : subst_typing (sub_elam s) (eextend t1 g1) (eextend (tsubst s t1) g2) = elam_hs s t1 hs in
let hk1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk1 hs in
let hk2g2 : kinding (eextend (tsubst s t1) g2) (tsubst (sub_elam s) t2) KType = kinding_substitution (sub_elam s) hk2 hsext in
let hkpg2 : kinding (eextend (tsubst s t1) g2) (tsubst (sub_elam s) phi) (k_m m (tsubst (sub_elam s) t2)) = subst_on_k_m (sub_elam s) m t2; kinding_substitution (sub_elam s) hkp hsext in
let hvg2 : validity (eextend (tsubst s t1) g2) (monotonic m (tsubst (sub_elam s) t2) (tsubst (sub_elam s) phi)) = subst_on_monotonic (sub_elam s) m t2 phi; validity_substitution (sub_elam s) hv hsext in
KArr #g2 #(tsubst s t1) #(tsubst (sub_elam s) t2) #(tsubst (sub_elam s) phi) #m hk1g2 hk2g2 hkpg2 hvg2
| KTLam #g #k #t #k' hw hk ->
let hwg2 : kwf g2 (ksubst s k) = kwf_substitution s hw hs in
let hkg2 : kinding (textend (ksubst s k) g2) (tsubst (sub_tlam s) t) (ksubst (sub_tlam s) k') = kinding_substitution (sub_tlam s) hk (tlam_hs s k hs) in
KTLam #g2 #(ksubst s k) #(tsubst (sub_tlam s) t) #(ksubst (sub_tlam s) k') hwg2 hkg2
| KELam #g #t1 #t2 #k2 hk1 hk2 ->
let hk1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk1 hs in
let hk2g2 : kinding (eextend (tsubst s t1) g2) (tsubst (sub_elam s) t2) (ksubst (sub_elam s) k2) = kinding_substitution (sub_elam s) hk2 (elam_hs s t1 hs) in
KELam hk1g2 hk2g2
| KTApp #g #t1 #t2 #k k' hk1 hk2 hw ->
let hk1g2:kinding g2 (tsubst s t1) (KKArr (ksubst s k) (ksubst (sub_tlam s) k')) = kinding_substitution s hk1 hs in
let hk2g2:kinding g2 (tsubst s t2) (ksubst s k) = kinding_substitution s hk2 hs in
let hwg2:kwf g2 (ksubst_tbeta (tsubst s t2) (ksubst (sub_tlam s) k')) = ksubst_on_tbeta s t2 k'; kwf_substitution s hw hs in
KTApp #g2 #(tsubst s t1) #(tsubst s t2) #(ksubst s k) (ksubst (sub_tlam s) k') hk1g2 hk2g2 hwg2
| KEApp #g #t #t' #k #e hk ht hw ->
let hkg2 : kinding g2 (tsubst s t) (KTArr (tsubst s t') (ksubst (sub_elam s) k)) = kinding_substitution s hk hs in
let htg2 : typing g2 (esubst s e) (tot (tsubst s t'))= subst_on_tot s t'; typing_substitution s ht hs in
let hwg2 : kwf g2 (ksubst_ebeta (esubst s e) (ksubst (sub_elam s) k)) = ksubst_on_ebeta s e k; kwf_substitution s hw hs in
let hwg2' : kinding g2 (TEApp (tsubst s t) (esubst s e)) (ksubst s (ksubst_ebeta e k)) = ksubst_on_ebeta s e k; KEApp hkg2 htg2 hwg2 in
hwg2'
| KSub #g #t #k' #k hk hsk ->
let plouf : kinding g2 (tsubst s t) (ksubst s k') = kinding_substitution s hk hs in
KSub #g2 #(tsubst s t) #(ksubst s k') #(ksubst s k) plouf (skinding_substitution #g1 s hsk hs)
(*SF : I get an error without 'plouf' : expected type (something); got type (something){refinement}. Why ?*)
(*SF : I switched to the new version of the substitution lemma because of this case ^*)
and skinding_substitution g1 k1 k2 s g2 h1 hs =
match h1 with
| KSubRefl #g #k hw ->
 KSubRefl (kwf_substitution s hw hs)
| KSubKArr #g #k1 #k2 k1' k2' hs21 hs12' hkwf11' ->
let hs21g2 : skinding g2 (ksubst s k2) (ksubst s k1)  = skinding_substitution s hs21 hs in
let hs12'g2 : skinding (textend (ksubst s k2) g2) (ksubst (sub_tlam s) k1') (ksubst (sub_tlam s) k2')  = skinding_substitution (sub_tlam s) hs12' (tlam_hs s k2 hs) in
let hkwf11'g2 : kwf g2 (ksubst s (KKArr k1 k1')) = kwf_substitution s hkwf11' hs in
KSubKArr (ksubst (sub_tlam s) k1') (ksubst (sub_tlam s) k2') hs21g2 hs12'g2 hkwf11'g2
| KSubTArr #g #t1 #t2 #k1 #k2 hs21 hs12' hkwf1 ->
let hs21g2 : styping g2 (tsubst s t2) (tsubst s t1)  = styping_substitution s hs21 hs in
let hs12'g2 : skinding (eextend (tsubst s t2) g2) (ksubst (sub_elam s) k1) (ksubst (sub_elam s) k2)  = skinding_substitution (sub_elam s) hs12' (elam_hs s t2 hs) in
let hkwf1g2 : kwf g2 (ksubst s (KTArr t1 k1)) = kwf_substitution s hkwf1 hs in
let hr : skinding g2 (KTArr (tsubst s t1) (ksubst (sub_elam s) k1)) (KTArr (tsubst s t2) (ksubst (sub_elam s) k2)) = KSubTArr hs21g2 hs12'g2 hkwf1g2 in
hr
and kwf_substitution g1 k s g2 h1 hs =
match h1 with
| WfType g -> WfType g2
| WfTArr #g #t #k' hk hw ->
let plouf : kinding g2 (tsubst s t) KType = (kinding_substitution s hk hs) in
WfTArr plouf (kwf_substitution (sub_elam s) hw (elam_hs s t hs))
(*SF : I also need plouf here. Why ?*)
| WfKArr #g #k #k' hw hw' ->
WfKArr (kwf_substitution s hw hs) (kwf_substitution (sub_tlam s) hw' (tlam_hs s k hs))
and validity_substitution g1 t1 s g2 h1 hs =
magic()(*
match h1 with
| VConstr #g #e #t #wp ht ->
(let htg2 : typing g2 (esubst s e) (Cmp EfPure (tsubst s t) (tsubst s wp)) = typing_substitution s ht hs in
let hr : validity g2 (tsubst s (tconstr e t wp)) = subst_on_tconstr s e t wp; VConstr htg2 in hr)
| VRedE #g #e #t #e' ht ht' hst ->
(
 let ht2 : typing g2 (esubst s e) (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht hs in
 let ht2' : typing g2 (esubst s e') (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht' hs in
 let hst2 : epstep (esubst s e) (esubst s e') = epstep_substitution s e e' hst in
 VRedE ht2 ht2' hst2
)
| VEqReflE #g #e #t ht ->
(let ht2:typing g2 (esubst s e) (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht hs in
    let hr:validity g2 (teqe (tsubst s t) (esubst s e) (esubst s e)) = VEqReflE #g2 #(esubst s e) #(tsubst s t) ht2 in
subst_on_teqe s (t) (e) (e);hr )
| VSubstE #g #e1 #e2 #t' t hv12 ht1 ht2 hk hvsub ->
(*This one is making the others fail*)
(
 let hv12g2 : validity g2 (teqe (tsubst s t') (esubst s e1) (esubst s e2)) = subst_on_teqe s t' e1 e2; validity_substitution #g1 #(teqe t' e1 e2) s #g2 hv12 hs in
 let ht1g2 : typing g2 (esubst s e1) (tot (tsubst s t')) = subst_on_tot s t'; typing_substitution #g1 #e1 s #g2 ht1 hs in
 let ht2g2 : typing g2 (esubst s e2) (tot (tsubst s t')) = subst_on_tot s t'; typing_substitution #g1 #e2 s #g2 ht2 hs in
 let hsext : subst_typing (sub_elam s) (eextend t' g1) (eextend (tsubst s t') g2) = elam_hs #g1 s #g2 t' hs in
 let hkg2 : kinding (eextend (tsubst s t') g2) (tsubst (sub_elam s) t) KType = kinding_substitution #(eextend t' g1) #t (sub_elam s) #(eextend (tsubst s t') g2) hk hsext in
 let hvsubg2 : validity g2 (tsubst_ebeta (esubst s e1) (tsubst (sub_elam s) t)) = tsubst_on_ebeta s e1 t; validity_substitution s hvsub hs in
 let hr : validity g2 (tsubst_ebeta (esubst s e2) (tsubst (sub_elam s) t)) = VSubstE #g2 #(esubst s e1) #(esubst s e2) #(tsubst s t') (tsubst (sub_elam s) t) hv12g2 ht1g2 ht2g2 hkg2 hvsubg2 in
 tsubst_on_ebeta s e2 t; hr
)
| VRedT #g #t #t' #k hk hk' hst ->
(let hkg2 : kinding g2 (tsubst s t) (ksubst s k) = kinding_substitution s hk hs in
let hk'g2 : kinding g2 (tsubst s t') (ksubst s k) = kinding_substitution s hk' hs in
let hstg2 : tstep (tsubst s t) (tsubst s t') = tstep_substitution s t t' hst in
let hr : validity g2 (teqt (ksubst s k) (tsubst s t) (tsubst s t')) = VRedT #g2 #(tsubst s t) #(tsubst s t') #(ksubst s k) hkg2 hk'g2 hstg2 in
subst_on_teqt s k t t'; hr)
| VEqReflT #g #t #k hk ->
(
let hkg2 : kinding g2 (tsubst s t) (ksubst s k) = kinding_substitution s hk hs in
let hr : validity g2 (teqt (ksubst s k) (tsubst s t) (tsubst s t)) = VEqReflT hkg2 in
  subst_on_teqt s k t t; hr)
| VSubstT #g #t1 #t2 #k t hv12 hkw hk hvsub ->
(
let hv12g2 : validity g2 (teqt (ksubst s k) (tsubst s t1) (tsubst s t2)) = subst_on_teqt s k t1 t2; validity_substitution #g1 #(teqt k t1 t2) s #g2 hv12 hs in
let hkwg2 : kwf g2 (ksubst s k) = kwf_substitution #g1 #k s #g2 hkw hs in
let hsext : subst_typing (sub_tlam s) (textend k g1) (textend (ksubst s k) g2) = tlam_hs #g1 s #g2 k hs in
let hkg2 : kinding (textend (ksubst s k) g2) (tsubst (sub_tlam s) t) KType = kinding_substitution #(textend k g1) #t (sub_tlam s) #(textend (ksubst s k) g2) hk hsext in
let hvsubg2 : validity g2 (tsubst_tbeta (tsubst s t1) (tsubst (sub_tlam s) t)) = tsubst_on_tbeta s t1 t; validity_substitution #g1 #(tsubst_tbeta t1 t) s #g2 hvsub hs in
let hr:validity g2 (tsubst_tbeta (tsubst s t2) (tsubst (sub_tlam s) t)) = VSubstT #g2 #(tsubst s t1) #(tsubst s t2) #(ksubst s k) (tsubst (sub_tlam s) t) hv12g2 hkwg2 hkg2 hvsubg2 in
tsubst_on_tbeta s t2 t; hr
)
| VSelAsHeap #g #h #l hth htl ->
(
    let hthg2 : typing g2 (eheap h) (tot theap) = subst_on_tot s theap; typing_substitution #g1 #(eheap h) s #g2 hth hs in
    let htlg2 : typing g2 (eloc l) (tot tref) = subst_on_tot s tref; typing_substitution #g1 #(eloc l) s #g2 htl hs in
    let hr : validity g2 (teqe tint (esel (eheap h) (eloc l)) (eint (h l))) = VSelAsHeap #g2 #h #l hthg2 htlg2 in
    subst_on_esel s (eheap h) (eloc l);
    subst_on_teqe s tint (esel (eheap h) (eloc l)) (eint (h l));
    hr
    )
| VUpdAsHeap #g #h #l #i hth htl hti ->
(
 let hthg2 : typing g2 (eheap h) (tot theap) = subst_on_tot s theap; typing_substitution s hth hs in
 let htlg2 : typing g2 (eloc l) (tot tref) = subst_on_tot s tref; typing_substitution s htl hs in
 let htig2 : typing g2 (eint i) (tot tint) = subst_on_tot s tint; typing_substitution s hti hs in
 let hr:validity g2 (teqe theap (eupd (eheap h) (eloc l) (eint i)) (eheap (upd_heap l i h))) = VUpdAsHeap hthg2 htlg2 htig2 in
 subst_on_eupd s (eheap h) (eloc l) (eint i);
 subst_on_teqe s theap (eupd (eheap h) (eloc l) (eint i)) (eheap (upd_heap l i h));
 hr

)
| VSelEq #g #eh #el #ei hth htl hti ->
(
 let hthg2 : typing g2 (esubst s eh) (tot theap) = subst_on_tot s theap; typing_substitution #g1 #eh s #g2 hth hs in
 let htlg2 : typing g2 (esubst s el) (tot tref) = subst_on_tot s tref; typing_substitution #g1 #el s #g2 htl hs in
 let htig2 : typing g2 (esubst s ei) (tot tint) = subst_on_tot s tint; typing_substitution #g1 #ei s #g2 hti hs in
 let hr : validity g2 (teqe tint (esel (eupd (esubst s eh) (esubst s el) (esubst s ei)) (esubst s el)) (esubst s ei)) = VSelEq #g2 #(esubst s eh) #(esubst s el) #(esubst s ei) hthg2 htlg2 htig2 in
 subst_on_eupd s eh el ei;
 subst_on_esel s (eupd eh el ei) el;
 subst_on_teqe s tint (esel (eupd eh el ei) el) ei;
 hr
 )
| VSelNeq #g #eh #el #el' #ei hth htl htl' hti hv ->
(
 let hthg2 : typing g2 (esubst s eh) (tot theap) = subst_on_tot s theap; typing_substitution s hth hs in
 let htlg2 : typing g2 (esubst s el) (tot tref) = subst_on_tot s tref; typing_substitution s htl hs in
 let htl'g2 : typing g2 (esubst s el') (tot tref) = subst_on_tot s tref; typing_substitution s htl' hs in
 let htig2 : typing g2 (esubst s ei) (tot tint) = subst_on_tot s tint; typing_substitution s hti hs in
 let hvg2 : validity g2 (tnot (teqe tloc (esubst s el) (esubst s el'))) = subst_on_tnot s (teqe tloc el el') ; subst_on_teqe s tloc el el';  validity_substitution s hv hs in
 let hr : validity g2 (teqe tint (esel (eupd (esubst s eh) (esubst s el') (esubst s ei)) (esubst s ei)) (esel (esubst s eh) (esubst s el))) = VSelNeq hthg2 htlg2 htl'g2 htig2 hvg2 in
 subst_on_esel s eh el;
 subst_on_eupd s eh el' ei;
 subst_on_esel s (eupd eh el' ei) ei;
 subst_on_teqe s tint (esel (eupd eh el' ei) ei) (esel eh el);
 hr
)
| VForallIntro #g #t #phi hk hv ->
(
 let hkg2 : kinding g2 (tsubst s t) KType = kinding_substitution s hk hs in
 let hvg2 : validity (eextend (tsubst s t) g2) (tsubst (sub_elam s) phi) = validity_substitution (sub_elam s) hv (elam_hs s t hs) in
 let hr : validity g2 (tforalle (tsubst s t) (tsubst (sub_elam s) phi)) = VForallIntro hkg2 hvg2 in
 subst_on_tforalle s t phi;
 hr

)
| VForallTypIntro #g #k #phi hkw hv ->
(
 let hkwg2 : kwf g2 (ksubst s k) = kwf_substitution s hkw hs in
 let hvg2 : validity (textend (ksubst s k) g2) (tsubst (sub_tlam s) phi) = validity_substitution (sub_tlam s) hv (tlam_hs s k hs) in
 let hr : validity g2 (tforallt (ksubst s k) (tsubst (sub_tlam s) phi)) = VForallTypIntro hkwg2 hvg2 in
 subst_on_tforallt s k phi;
 hr
)
| VForallElim #g #t #phi #e hv ht ->
(
 let hvg2 : validity g2 (tforalle (tsubst s t) (tsubst (sub_elam s) phi)) = subst_on_tforalle s t phi; validity_substitution s hv hs in
 let htg2 : typing g2 (esubst s e) (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht hs in
 let hr : validity g2 (tsubst_ebeta (esubst s e) (tsubst (sub_elam s) phi)) = VForallElim hvg2 htg2 in
 tsubst_on_ebeta s e phi;
 hr
)
| VForallTypElim #g #t #k #phi hv hk ->
(
 let hvg2 : validity g2 (tforallt (ksubst s k) (tsubst (sub_tlam s) phi)) = subst_on_tforallt s k phi; validity_substitution s hv hs in
 let hkg2 : kinding g2 (tsubst s t) (ksubst s k) =kinding_substitution s hk hs in
 let hr : validity g2 (tsubst_tbeta (tsubst s t) (tsubst (sub_tlam s) phi)) = VForallTypElim hvg2 hkg2 in
 tsubst_on_tbeta s t phi;
 hr
)
| VAndElim1 #g #p1 #p2 hv ->
(
 let hvg2 : validity g2 (tand (tsubst s p1) (tsubst s p2)) = subst_on_tand s p1 p2; validity_substitution s hv hs in
 VAndElim1 hvg2
)
| VAndElim2 #g #p1 #p2 hv ->
(
 let hvg2 : validity g2 (tand (tsubst s p1) (tsubst s p2)) = subst_on_tand s p1 p2; validity_substitution s hv hs in
 VAndElim2 hvg2
)
| VAndIntro #g #p1 #p2 hv1 hv2 ->
(
 let hv1g2 : validity g2 (tsubst s p1) = validity_substitution s hv1 hs in
 let hv2g2 : validity g2 (tsubst s p2) = validity_substitution s hv2 hs in
 subst_on_tand s p1 p2 ;VAndIntro hv1g2 hv2g2
)
| VExMiddle #g #t1 #t2 hk1 hk2 hv1 hv2 ->
(
 let hk1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk1 hs in
 let hk2g2 : kinding g2 (tsubst s t2) KType = kinding_substitution s hk2 hs in
 let hsext : subst_typing (sub_elam s) (eextend t1 g1) (eextend (tsubst s t1) g2) = elam_hs #g1 s #g2 t1 hs in
 let hsextnot : subst_typing (sub_elam s) (eextend (tnot t1) g1) (eextend (tsubst s (tnot t1)) g2) = elam_hs #g1 s #g2 (tnot t1) hs in
 let hv1g2 : validity (eextend (tsubst s t1) g2) (tesh (tsubst s t2)) = tsubst_elam_shift s t2; validity_substitution (sub_elam s) hv1 hsext in
 let hv2g2 : validity (eextend (tnot (tsubst s t1)) g2) (tesh (tsubst s t2)) = subst_on_tnot s t1; tsubst_elam_shift s t2; validity_substitution (sub_elam s) hv2 hsextnot in
 VExMiddle hk1g2 hk2g2 hv1g2 hv2g2
)
| VOrIntro1 #g #t1 #t2 hv hk ->
(
 let hvg2 : validity g2 (tsubst s t1) = validity_substitution s hv hs in
 let hkg2 : kinding g2 (tsubst s t2) KType = kinding_substitution s hk hs in
 subst_on_tor s t1 t2; VOrIntro1 hvg2 hkg2
)
| VOrIntro2 #g #t1 #t2 hv hk ->
(
 let hvg2 : validity g2 (tsubst s t2) = validity_substitution s hv hs in
 let hkg2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk hs in
 subst_on_tor s t1 t2; VOrIntro2 hvg2 hkg2
)
| VOrElim #g #t1 #t2 #t3 hk1 hk2 hk3 hvor hv1 hv2 ->
(
 let hk1g2 : kinding g2 (tsubst s t1) KType = kinding_substitution s hk1 hs in
 let hk2g2 : kinding g2 (tsubst s t2) KType = kinding_substitution s hk2 hs in
 let hk3g2 : kinding g2 (tsubst s t3) KType = kinding_substitution s hk3 hs in
 let hvorg2 : validity g2 (tor (tsubst s t1) (tsubst s t2)) = subst_on_tor s t1 t2; validity_substitution s hvor hs in
 let hv1g2 : validity (eextend (tsubst s t1) g2) (tesh (tsubst s t3)) = tsubst_elam_shift s t3; validity_substitution (sub_elam s) hv1 (elam_hs s t1 hs) in
 let hv2g2 : validity (eextend (tsubst s t2) g2) (tesh (tsubst s t3)) = tsubst_elam_shift s t3; validity_substitution (sub_elam s) hv2 (elam_hs s t2 hs) in
 VOrElim hk1g2 hk2g2 hk3g2 hvorg2 hv1g2 hv2g2
)
| VFalseElim #g #t hv hk ->
(
 let hvg2 : validity g2 tfalse = validity_substitution s hv hs in
 let hkg2 : kinding g2 (tsubst s t) KType = kinding_substitution s hk hs in
 VFalseElim hvg2 hkg2
)
| VPreceedsIntro #g #v1 #v2 #t1 #t2 ht1 ht2 ->
(
 let ht1g2 : typing g2 (esubst s v1) (tot (tsubst s t1)) = subst_on_tot s t1; typing_substitution #g1 #v1 s #g2 ht1 hs in
 let ht2g2 : typing g2 (esubst s v2) (tot (tsubst s t2)) = subst_on_tot s t2; typing_substitution #g1 #v2 s #g2 ht2 hs in
 subst_on_tprecedes s t1 t2 v1 v2;
 VPreceedsIntro ht1g2 ht2g2
)
| VDistinctC #g #t #c1 #c2 ht1 ht2 ->
(let ht1g2 : typing g2 (EConst (ecsubst s c1)) (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht1 hs in
 let ht2g2 : typing g2 (EConst (ecsubst s c2)) (tot (tsubst s t)) = subst_on_tot s t; typing_substitution s ht2 hs in
 subst_on_teqe s t (EConst c1) (EConst c2); subst_on_tnot s (teqe t (EConst c1) (EConst c2)); VDistinctC #g2 #(tsubst s t) #(ecsubst s c1) #(ecsubst s c2) ht1g2 ht2g2)
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
| VInjTH #g #t1 #t2 #phi #t1' #t2' #phi' #m hv ->
(
 magic()
 (* SF : not up-to-date *)
 (*
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
 *)
)
*)
and elam_hs g1 s g2 t1 hs =
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
and tlam_hs g1 s g2 k hs =
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
#reset-options
//}}}

(****************************)
(* Replacement Lemma (beta) *)
(****************************)

//{{{

(*
val sub_einc_above : var -> Tot sub
let sub_einc_above n =
Sub (fun x -> if x >= n then EVar (x+1) else EVar x) tsub_id

val sub_ebeta_gen : var -> e:exp -> Tot sub
let sub_ebeta_gen n e=
  Sub (fun x -> if x < n then EVar x else if x = n then e else EVar (x-1)) tsub_id

let teshab n = tsubst (sub_einc_above n)
let keshab n = ksubst (sub_einc_above n)

val eextendg : nat -> typ -> env -> Tot env
let eextendg n t e =
  let Env eenvi tenvi = e in
  let eenvi' : eenv = fun x -> if x < n then omap (teshab n) (eenvi x) else
                               if x = n then Some (teshab n t)
                                        else omap (teshab n) (eenvi (x-1))
  in
  let tenvi' : tenv = fun x -> omap (keshab n) (tenvi x) in
  Env eenvi' tenvi'
val envsubst_ebeta : n:var -> e:exp -> g:env ->
   Tot (env)
let envsubst_ebeta n e g =
  let Env eenvi tenvi = e in
  let eenvi' : eenv = fun x -> omap (tsubst (sub_ebeta_gen n e)) (eenvi x)
  in
  let tenvi' : tenv = fun x -> omap (ksubst (sub_ebeta_gen n e)) (tenvi x) in
  Env eenvi' tenvi'


opaque val typing_replace : #g:env -> #e:exp -> #c:cmp ->
                     #e1:exp -> #e2:exp -> #tbeta:typ ->
                     ht1 : typing g e1 (tot tbeta) ->
		     ht2 : typing g e2 (tot tbeta) ->
		     hv : validity g (teqe tbeta e1 e2) ->
		     ht : typing g (esubst_ebeta e1 e) (csubst_ebeta e1 c) ->
		     Tot (typing g (esubst_ebeta e2 e) (csubst_ebeta e2 c))
(decreases %[ht])
let rec typing_replace g e c e1 e2 t ht1 ht2 hv ht =
match ht with
| TySub #x1 #x2 #c' #c ht' hsc -> admit()
| TyRet #x1 #x2 t htot -> admit()
| _ ->
(
 match e with
 | EVar x ->
 (
(* SF : Oups … *)
 )
)
*)
//}}}

(******************)
(* skinding arrow *)
(******************)

opaque val skinding_hs : #g:env -> k:knd -> k':knd ->
                 hsk:skinding g k k' ->
		 Tot(subst_typing sub_id (textend k' g) (textend k g))
let skinding_hs g k k' hsk =
let gext = textend k g in
let hskext : skinding gext (ktsh k) (ktsh k') = skinding_substitution sub_tinc hsk (hs_sub_tinc g k) in
SubstTyping sub_id (textend k' g) (textend k g)
(fun x -> tsubst_with_sub_id (Some.v (lookup_evar (textend k' g) x)); TyVar x)
(fun a -> match a with
  | 0 -> let hk : kinding (textend k g) (TVar 0) (ktsh k) = KVar #(textend k g) 0 in
         let hk' : kinding (textend k g) (TVar 0) (ktsh k') = KSub hk hskext in
	 (ksubst_with_sub_id (ktsh k'); hk')
  | _ -> (ksubst_with_sub_id (Some.v (lookup_tvar (textend k' g) a)); KVar a)
)

(********************)
(* ewf manipulation *)
(********************)
//{{{
opaque val get_kinding_from_ewf : #g:env -> hw:ewf g -> x:var{is_Some (lookup_evar g x)} ->
                           Tot (kinding g (Some.v (lookup_evar g x)) KType)
(decreases %[hw])
let rec get_kinding_from_ewf g hw x =
let None = lookup_evar empty x in
match hw with
| GType #gsub #tsub hwsub hksub ->
(
 if x = 0 then kinding_substitution sub_einc hksub (hs_sub_einc gsub tsub)
 else let hksub' : kinding gsub (Some.v (lookup_evar gsub (x-1))) KType = get_kinding_from_ewf hwsub (x-1) in kinding_substitution sub_einc hksub' (hs_sub_einc gsub tsub)
)
| GKind #gsub #ksub hwsub hkwfsub ->
(
 let hksub : kinding gsub (Some.v (lookup_evar gsub x)) KType = get_kinding_from_ewf hwsub x in
 kinding_substitution sub_tinc hksub (hs_sub_tinc gsub ksub)

)
opaque val get_kwf_from_ewf : #g:env -> hewf: ewf g -> a:var{is_Some (lookup_tvar g a)} ->
                       Tot (kwf g (Some.v (lookup_tvar g a)))
(decreases %[hewf])
let rec get_kwf_from_ewf g hewf a =
let None = lookup_tvar empty a in
match hewf with
| GType #gsub #tsub hwsub _ ->
(
 let hkwfsub : kwf gsub (Some.v (lookup_tvar gsub a)) = get_kwf_from_ewf hwsub a in
 kwf_substitution sub_einc hkwfsub (hs_sub_einc gsub tsub)
)
| GKind #gsub #ksub hwsub hkwfsub ->
(
 if a = 0 then kwf_substitution sub_tinc hkwfsub (hs_sub_tinc gsub ksub)
 else let hkwfsub' : kwf gsub (Some.v (lookup_tvar gsub (a-1))) = get_kwf_from_ewf hwsub (a-1) in
 kwf_substitution sub_tinc hkwfsub' (hs_sub_tinc gsub ksub)
)
//}}}

(************************)
(* kinding manipulation *)
(************************)

//{{{
(* This takes forever to typecheck and fails without the assert;
   plus this fails without the explicit type annotation on k' in KTApp
   (Unresolved implicit argument). Filed as #237.
opaque val kdg_foralle : #g:env -> #t1:typ -> #t2:typ ->
                =hk1:kinding g t1 KType ->
                =hk2:kinding (eextend t1 g) t2 KType ->
                Tot (kinding g (TTApp (TConst TcForallE) t1)
                               (KKArr (KTArr t1 KType) KType))
let kdg_foralle g t1 t2 hk1 hk2 =
  let gwf = kinding_ewf hk1 in
  (* assert(KKArr (KTArr t1 KType) KType =  *)
  (*        ktsubst_beta t1 (KKArr (KTArr (TVar 0) KType) KType)); *)
  KTApp (KKArr (KTArr (TVar 0) KType) KType) (KConst TcForallE gwf) hk1 (magic())
*)

opaque val kdg_foralle : #g:env -> #t1:typ -> #t2:typ ->
                =hk1:kinding g t1 KType ->
                =hk2:kinding (eextend t1 g) t2 KType ->
                Tot (kinding g (tforalle t1 t2) KType)
let kdg_foralle g t1 t2 hk1 hk2 = admit()
(* TODO: finish this -- it takes >10s to check (admitting)
  let gwf = kinding_ewf hk1 in
  let tres x = KKArr (KTArr x KType) KType in
     (* using tres doesn't work, god damn it! Had to unfold it. File this shit. *)
  let happ1 : (kinding g (TTApp (TConst TcForallE) t1)
                         (KKArr (KTArr t1 KType) KType)) =
    KTApp (KKArr (KTArr (TVar 0) KType) KType) (KConst TcForallE gwf) hk1 (magic())
          (* (WfKArr (magic()) (*WfTArr (magic())*) *)
          (*                 (WfType (eextend (TVar 0) g)) *)
          (*         (WfType (textend KType g))) *)
  in magic() (* KTApp KType happ1 hk2 (WfType g) *)
*)

opaque val kdg_impl : #g:env -> #t1:typ -> #t2:typ ->
            =hk1:kinding g t1 KType ->
            =hk2:kinding g t2 KType ->
            Tot (kinding g (timpl t1 t2) KType)
let kdg_impl g t1 t2 hk1 hk2 = admit()
(* TODO: this needs updating:
  let happ1 : (kinding g (TTApp (TConst TcImpl) t1) (KKArr KType KType)) =
    KTApp (KKArr KType KType) (KConst g TcImpl) hk1
          (WfKArr (WfType g) (WfType (textend g KType)))
  in KTApp KType happ1 hk2 (WfType g)
*)

opaque val kdg_false : g:env -> Tot (kinding g tfalse KType)
let kdg_false g = KConst (WFTcOther g TcFalse)

opaque val kdg_not : #g:env -> #t:typ ->
           =hk:kinding g t KType ->
           Tot (kinding g (tnot t) KType)
let kdg_not g t hk = kdg_impl hk (kdg_false g)
opaque val kdg_tot_wp : #g:env -> #t:typ -> kinding g t KType -> Tot (kinding g (tot_wp t) (k_m EfPure t))
let kdg_tot_wp g t hk = admit()

opaque val kdg_ite : #g:env -> m:eff -> t:typ -> #wp0:typ -> #wp1:typ -> #wp2:typ ->
            kinding g wp0 (k_m m tint) ->
	    kinding g wp1 (k_m m t) ->
	    kinding g wp2 (k_m m t) ->
	    Tot (kinding g (ite m t wp0 wp1 wp2) (k_m m t))
let kdg_ite g m t wp0 wp1 wp2 hk0 hk1 hk2 = admit()

opaque val kdg_return_pure : #g:env -> #e:exp -> #t:typ ->
   typing g e (tot t) ->
   kinding g t KType ->
   Tot (kinding g (return_pure t e) (k_pure t))
let kdg_return_pure g e t ht hk =
   let gext = textend (k_post_pure t) g in
   let hkbody : kinding gext (TEApp (TVar 0) (etsh e)) KType =
     let hkt : kinding gext (TVar 0) (k_post_pure (ttsh t)) = KVar 0 in
     let ht  : typing gext (etsh e) (tot (ttsh t)) = subst_on_tot sub_tinc t; typing_substitution sub_tinc ht (hs_sub_tinc g (k_post_pure t)) in
     KEApp #gext #(TVar 0) #(ttsh t) #(KType) #(etsh e) hkt ht (WfType gext)
   in
   let hkw : kwf g (k_post_pure t) = WfTArr hk (WfType (eextend t g)) in
   KTLam hkw hkbody

opaque val kdg_tint : g:env -> Tot (kinding g tint KType)
let kdg_tint g = KConst #g #TcInt (WFTcOther g TcInt)

opaque val kdg_tb : g:env -> tc:tconst{is_TcInt tc \/ is_TcHeap tc \/ is_TcRefInt tc} ->
   Tot (kinding g (TConst tc) KType)
let kdg_tb g tc = admit()

opaque val kdg_econst : g:env -> ec:econst -> hwf : ecwf g ec -> Tot (kinding g (econsts ec) KType)
let kdg_econst g ec hwf = admit()


//}}}

(*************************)
(* Type level inversions *)
(*************************)

//{{{
type inversion_tarr_res : env -> typ -> eff -> typ -> typ -> Type =
| InversionTArr : #g:env -> #targ : typ -> #m:eff -> #tret:typ -> #wp:typ ->
                  kinding g targ KType ->
		  kinding (eextend targ g) tret KType ->
		  kinding (eextend targ g) wp (k_m m tret) ->
		  validity (eextend targ g) (monotonic m tret wp) ->
		  inversion_tarr_res g targ m tret wp
opaque val inversion_tarr : #g:env -> #targ:typ -> #m:eff -> #tret:typ -> #wp:typ ->
                     hk:kinding g (TArr targ (Cmp m tret wp)) KType ->
		     Tot (inversion_tarr_res g targ m tret wp)
(decreases %[hk])
let rec inversion_tarr g targ m tret wp hk =
match hk with
| KArr #g #t1 #t2 #phi #m hk1 hk2 hkp hv -> InversionTArr (hk1) (hk2) (hkp) (hv)
| KSub #g #t #k' #k hk hs ->
  let KSubRefl hw = hs in inversion_tarr hk


//}}}

(**************************************)
(* (small) Derived Validity Judgments *)
(**************************************)
//{{{
opaque val v_impl_intro : #g:env -> t1:typ -> t2:typ ->
                   =hk:kinding g t1 KType ->
                   =hv:validity (eextend t1 g) (tesh t2) ->
                  Tot (validity g (timpl t1 t2))
let v_impl_intro g t1 t2 hk hv= VForallIntro hk hv

opaque val v_impl_elim : #g:env -> #t1:typ -> #t2:typ ->
                 =hv12:validity g (timpl t1 t2) ->
                 =hv1 :validity g t1 ->
                  Tot (validity g t2)
let v_impl_elim g t1 t2 hv12 hv1 = admit()

opaque val v_assume : g:env -> x:var{is_Some (lookup_evar g x)} ->
  Tot (validity g (Some.v (lookup_evar g x)))
let v_assume g x = magic()

assume opaque val v_true : #g:env -> =hewf:ewf g -> Tot (validity g ttrue)
(* VAssume changed *)
(* let v_true g hewf = v_impl_intro tfalse tfalse *)
(*                             (VAssume 0 (GType (kdg_false hewf))) *)

    (* CH: Can probably derive V-ExMiddle from: *)

    (* G, _:~t |= t *)
    (* ----------- [V-Classical] *)
    (* G |= t *)

    (*     of, even better, from this *)

    (* G, _:~t |= false *)
    (* --------------- [V-Classical] *)
    (* G |= t *)

(* Should follow without VExMiddle *)
opaque val v_not_not_intro : #g:env -> #t:typ ->
                      =hv:validity g t ->
                          Tot(validity g (tnot (tnot t)))
let v_not_not_intro g t hv = admit()

(* Should follow from VExMiddle (it's equivalent to it) *)
opaque val v_not_not_elim : #g:env -> t:typ ->
                     =hv:validity g (tnot (tnot t)) ->
                         Tot(validity g t)
let v_not_not_elim g t hv = admit()

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
opaque val v_or_intro1 : #g:env -> #t1:typ -> #t2:typ ->
                  =hv1:validity g t1 ->
                  =hk2:kinding g t2 KType ->
                       Tot(validity g (tor t1 t2))
let v_or_intro1 g t1 t2 hv1 hk2 = magic()
  (*
  v_impl_intro (tnot t1) t2
               (magic())
	       *)

opaque val v_or_intro2 : #g:env -> #t1:typ -> #t2:typ ->
                  =hv:validity g t2 ->
                  =hk:kinding g t1 KType ->
                      Tot(validity g (tor t1 t2))
let v_or_intro2 g t1 t2 hv hk = admit()

(* CH: TODO: so far didn't manage to derive this on paper,
             might need to add it back as primitive! *)
opaque val v_or_elim : #g:env -> t1:typ -> t2:typ -> #t3:typ ->
                =hv :validity g (tor t1 t2) ->
                =hv1:validity (eextend t1 g) (tesh t3) ->
                =hv2:validity (eextend t2 g) (tesh t3) ->
                =hk :kinding g t3 KType ->
                     Tot(validity g t3)
let v_or_elim g t1 t2 t3 hv hv1 hv2 hk = admit()

(* CH: TODO: prove symmetry and transitivity of equality as in the F7
   paper from VEqRefl and VSubst; this will save us 4 rules *)
(*
opaque val v_eq_trane : #g:env -> #e1:exp -> #e2:exp -> #e3:exp ->
             =hv12:validity g (teqe e1 e2) ->
             =hv23:validity g (teqe e2 e3) ->
                   validity g (teqe e1 e3)
let v_eq_trane = admit()

opaque val v_eq_syme : #g:env -> #e1:exp -> #e2:exp ->
             =hv:validity g (teqe e1 e2) ->
                 validity g (teqe e2 e1)
let v_eq_syme = admit()
*)

opaque val v_eq_trant : #g:env -> #t1:typ -> #t2:typ -> #t3:typ -> #k:knd ->
             =hv12:validity g (teqt k t1 t2) ->
             =hv23:validity g (teqt k t2 t3) ->
                   Tot(validity g (teqt k t1 t3))
let v_eq_trant g t1 t2 t3 k hv12 hv23 = admit()

opaque val v_eq_symt : #g:env -> #t1:typ -> #t2:typ -> #k:knd ->
            =hv:validity g (teqt k t1 t2) ->
                Tot(validity g (teqt k t2 t1))
let v_eq_symt g t1 t2 k hv = admit()

opaque val v_inv_foralle : #g:env -> t:typ -> phi:typ ->
                    validity g (tforalle t phi) ->
	            Tot(validity (eextend t g) phi)
let v_inv_foralle g t phi hv =
let hs : subst_typing sub_einc g (eextend t g) = hs_sub_einc g t in
let hvext : validity (eextend t g) (tforalle (tesh t) (tsubst (sub_elam sub_einc) phi) ) = subst_on_tforalle sub_einc t phi; validity_substitution sub_einc hv hs in
let hvext' : validity (eextend t g) (tsubst_ebeta (EVar 0) (tsubst (sub_elam sub_einc) phi)) = VForallElim #(eextend t g) #(tesh t) #(tsubst (sub_elam sub_einc) phi) #(EVar 0) hvext (TyVar 0) in
let hvext'' : validity (eextend t g) phi =
tsubst_ebeta_elam_einc phi; hvext' in
hvext''
//}}}

(******************)
(* Derived Lemmas *)
(******************)
//{{{
type typing_der : g:env -> m:eff -> t:typ -> wp:typ -> Type =
| TypingDerived : #g:env -> #m:eff -> #t:typ -> #wp:typ ->
                  hkt : kinding g t KType ->
		  hkwp : kinding g wp (k_m m t) ->
		  validity g (monotonic m t wp) ->
		  typing_der g m t wp
type scmp_der : g:env -> m':eff -> t':typ -> wp':typ -> m:eff -> t:typ -> wp:typ -> Type =
| ScmpDerived : #g:env -> #m':eff -> #t':typ -> #wp':typ ->
                        #m:eff  -> #t:typ  -> #wp:typ ->
                        kinding g t' KType ->
			kinding g wp' (k_m m' t') ->
                        kinding g t KType ->
			kinding g wp (k_m m t) ->
			scmp_der g m' t' wp' m t wp

#set-options "--split_cases 1"

opaque val typing_derived : #g:env -> #e:exp -> #m:eff -> #t:typ -> #wp:typ ->
                     hwf : ewf g ->
                     ht : typing g e (Cmp m t wp) ->
		     Tot (typing_der g m t wp)
(decreases %[ht])
opaque val scmp_derived : #g:env -> #m':eff -> #t':typ -> #wp':typ ->
                             #m:eff -> #t:typ -> #wp:typ ->
                             hwf : ewf g ->
                             hsc : scmp g (Cmp m' t' wp') (Cmp m t wp) ->
                             Tot (scmp_der g m' t' wp' m t wp )
(decreases %[hsc])
opaque val kinding_derived : #g:env -> #t:typ -> #k:knd ->
                      hwf:ewf g ->
                      hkt:kinding g t k ->
		      Tot (kwf g k)
(decreases %[hkt])
opaque val styping_derived : #g:env -> #t':typ -> #t:typ ->
		      hst:styping g t' t ->
		      Tot (cand (kinding g t' KType) (kinding g t KType))
(decreases %[hst])
opaque val skinding_derived : #g:env -> #k:knd -> #k':knd ->
		       hsk:skinding g k k' ->
		       Tot (cand (kwf g k) (kwf g k'))
(decreases %[hsk])

let rec typing_derived g e m t wp hwf ht =
match ht with
| TyVar #g x ->
 (
  let t = Some.v (lookup_evar g x) in
  let hkt : kinding g t KType = get_kinding_from_ewf hwf x in
  let hkwp : kinding g (tot_wp t) (k_m EfPure t) = kdg_tot_wp hkt in
  let hmono : validity g (monotonic EfPure t (tot_wp t)) = magic() in
  TypingDerived hkt hkwp hmono
 )
| TyConst g c hecwf -> admit()
| TyAbs #g #t1 #ebody m t2 wp hk ht ->
(
 let hwfext = GType hwf hk in
 let TypingDerived hkt2 hkwp hmono : typing_der (eextend t1 g) m t2 wp = typing_derived hwfext ht in
 let tarr = TArr t1 (Cmp m t2 wp) in
 let hktarr : kinding g tarr KType = KArr hk hkt2 hkwp hmono in
 let hkwp  : kinding g (tot_wp tarr) (k_m EfPure tarr) = kdg_tot_wp hktarr in
 let hmono : validity g (monotonic EfPure tarr (tot_wp tarr)) = magic() in
 TypingDerived hktarr hkwp hmono
)
| TyIf0 g e0 e1 e2 m t wp0 wp1 wp2 hte0 hte1 hte2 ->
(
 let TypingDerived hktint hkwp0 hmono0 : typing_der g m tint wp0 = typing_derived hwf hte0 in
 let TypingDerived hkt hkwp1 hmono1 : typing_der g m t wp1 = typing_derived hwf hte1 in
 let TypingDerived _ hkwp2 hmono2 : typing_der g m t wp2 = typing_derived hwf hte2 in
 let hkite : kinding g (ite m t wp0 wp1 wp2) (k_m m t) = kdg_ite m t hkwp0 hkwp1 hkwp2 in
 let hmono : validity g (monotonic m t (ite m t wp0 wp1 wp2)) = magic() in
 TypingDerived hkt hkite hmono

)
| TyApp #g #e1 #e2 #m #t #t' #wp #wp1 #wp2 ht1 ht2 htot hk ->
(
 let tarr = TArr t (Cmp m t' wp) in
 let tret = tsubst (sub_ebeta e2) t' in
 let wpret = tyapp_wp m e2 t t' wp wp1 wp2 in
 let TypingDerived hktarr hkwp1 hmono1 : typing_der g m tarr wp1 = typing_derived hwf ht1 in
 let TypingDerived hkt hkwp2 hmono2 : typing_der g m t wp2 = typing_derived hwf ht2 in
 let InversionTArr hktarg hkt' hkwp _ = inversion_tarr #g #t #m #t' #wp hktarr in
 if (teappears 0 t') then
   let Some htot2 = htot in
   let hktret : kinding g tret KType = kinding_substitution (sub_ebeta e2) hkt' (ebeta_hs htot2) in
   let hkwp : kinding g wpret (k_m m tret) = magic() in
   let hkmono : validity g (monotonic m tret wpret) = magic() in
   TypingDerived hktret hkwp hkmono
 else
   let hktret : kinding g tret KType = tsubst_with_almost_eq (edec_ebeta_almost_eq e2) t'; Some.v hk in
   let hkwp : kinding g wpret (k_m m tret) = magic() in
   let hkmono : validity g (monotonic m tret wpret) = magic() in
   TypingDerived hktret hkwp hkmono

)
| TyRet #g #e t ht ->
(
 let TypingDerived hkt _ _ : typing_der g EfPure t (tot_wp t) = typing_derived hwf ht in
 let hkwp : kinding g (return_pure t e) (k_m EfPure t) = kdg_return_pure #g #e #t ht hkt in
 let hmono : validity g (monotonic EfPure t (return_pure t e)) = magic () in
 TypingDerived hkt hkwp hmono
)
| TySub #g #e #c' #c ht' hsc ->
(
 let Cmp m t wp = c in
 let Cmp m' t' wp' = c' in
 let TypingDerived hkt' hkwp' _ : typing_der g m' t' wp' = typing_derived #g #e #m' #t' #wp' hwf ht' in
 let ScmpDerived hkt' hkwp' hkt hkwp : scmp_der g m' t' wp' m t wp = scmp_derived #g #m' #t' #wp' #m #t #wp hwf hsc  in
 let hmono : validity g (monotonic m t wp) = SCmp.hvmono hsc in
 TypingDerived hkt hkwp hmono
)
and scmp_derived g m' t' wp' m t wp hwf hsc =
let SCmp _ _ _ _  hssub hkwp hvmono hkwp' hvmono' hvsub = hsc in
let Conj hkt' hkt : cand (kinding g t' KType) (kinding g t KType) = styping_derived hssub in
ScmpDerived #g #m' #t' #wp' #m #t #wp hkt' hkwp' hkt hkwp
and styping_derived g t' t hst =
match hst with
| SubConv #g #t t' hv hk hk' -> Conj hk' hk
| SubFun #g #t #t' #c' #c hst hsc hk' ->
(
 (*g |- t -> c : KType*)
 let Cmp mc tc wpc = c in
 let Cmp mc' tc' wpc' = c' in
 let Conj hkt hkt' : cand (kinding g t KType) (kinding g t' KType) = styping_derived hst in
 let SCmp _ _ _ _ hstc'tc hkwpc hvmonowpc hkwpc' hvmonowpc' _ = hsc in
 let Conj hktc' hktc : cand (kinding (eextend t g) tc' KType) (kinding (eextend t g) tc KType) = styping_derived hstc'tc in
 let hv: validity (eextend t g) (monotonic mc tc wpc) = SCmp.hvmono hsc in
 let hktarr : kinding g (TArr t c) KType = KArr hkt hktc hkwpc hv in
 Conj hk' hktarr
)
| SubTrans #g #t1 #t2 #t3 hs12 hs23 ->
(
 let Conj hkt1 hkt2 = styping_derived hs12 in
 let Conj hkt2 hkt3 = styping_derived hs23 in
 Conj hkt1 hkt3
)
and kinding_derived g t k hwf hk =
match hk with
| KVar #g a -> get_kwf_from_ewf hwf a
| KConst #g #c htcwf -> admit()
| KArr #g #t1 #t2 #phi #m hk1 hk2 hkp hv -> WfType g
| KTLam #g #k #t #k' hw hk ->
(
 let hewfext : ewf (textend k g) = GKind hwf hw in
 let hbkwf : kwf (textend k g) k' = kinding_derived hewfext hk in
 WfKArr hw hbkwf
)
| KELam #g #t1 #t2 #k2 hk1 hk2 ->
(
 let hewfext : ewf (eextend t1 g) = GType hwf hk1 in
 let hbkwf : kwf (eextend t1 g) k2 = kinding_derived hewfext hk2 in
 WfTArr hk1 hbkwf
)
| KTApp #g #t1 #t #k k' hk1 hk2 hw -> hw
| KEApp #g #t #t' #k #e hk ht hw -> hw
| KSub #g #t #k' #k hk hs ->
(
 let Conj hkw1 hkw2 : cand (kwf g k') (kwf g k) = skinding_derived hs in
 hkw2
)
and skinding_derived g k k' hsk =
match hsk with
| KSubRefl hw -> Conj hw hw
(*
| KSubKArr : #g:env -> #k1:knd -> #k2:knd -> k1':knd -> k2':knd ->
             =hs21 :skinding g k2 k1 ->
	     =hkw:kwf g k2 ->
             =hs12':skinding (textend k2 g) k1' k2' ->
                    skinding g (KKArr k1 k1') (KKArr k2 k2')
		    *)
| KSubKArr #g #k1 #k2 k1' k2' hs21 hs12' hkwf1 ->
(
 let gext = textend k2 g in
 let Conj hkw2 hkw1 : cand (kwf g k2) (kwf g k1) = skinding_derived hs21 in
 let Conj hkw1' hkw2' : cand (kwf gext k1') (kwf gext k2') = skinding_derived hs12' in
 let hkwf2 : kwf g (KKArr k2 k2') = WfKArr hkw2 hkw2' in
 Conj hkwf1 hkwf2
)
| KSubTArr #g #t1 #t2 #k1 #k2 hs21 hs12' hkwf1 ->
(
 let gext = eextend t2 g in
 let Conj hk2 hk1 : cand (kinding g t2 KType) (kinding g t1 KType) = styping_derived hs21 in
 let Conj hkwf1' hkwf2' : cand (kwf gext k1) (kwf gext k2) = skinding_derived hs12' in
 let hkwf2 : kwf g (KTArr t2 k2) = WfTArr hk2 hkwf2' in
 Conj hkwf1 hkwf2
)

#reset-options
//}}}
(********************************************)
(* Subtyping/Subkinding Substitution Arrows *)
(********************************************)
//{{{
opaque val styping_hs : #g:env -> t:typ -> t':typ ->
		 hst: styping g t t' ->
		 Tot(subst_typing sub_id (eextend t' g) (eextend t g))
let styping_hs g t t' hst =
let Conj hk hk' = styping_derived #g #t #t' hst in
let gext = eextend t g in
let hstext : styping gext (tesh t) (tesh t') = styping_substitution sub_einc hst (hs_sub_einc g t) in
let hkext : kinding gext (tesh t) KType = kinding_substitution sub_einc hk (hs_sub_einc g t) in
let hk'ext : kinding gext (tesh t') KType = kinding_substitution sub_einc hk' (hs_sub_einc g t) in
let hkwp' : kinding gext (tot_wp (tesh t')) (k_pure (tesh t')) = kdg_tot_wp hk'ext in
let hvmono' : validity gext (monotonic EfPure (tesh t') (tot_wp (tesh t'))) = magic() in
let hkwp : kinding gext (tot_wp (tesh t)) (k_pure (tesh t)) = kdg_tot_wp hkext in
let hvmono : validity gext (monotonic EfPure (tesh t) (tot_wp (tesh t))) = magic() in
let hvsub : validity gext (sub_computation EfPure (tesh t') (tot_wp (tesh t')) EfPure (tesh t) (tot_wp (tesh t))) = magic() in
let hsc = SCmp EfPure (tot_wp (tesh t)) EfPure (tot_wp (tesh t')) hstext hkwp' hvmono' hkwp hvmono hvsub in
SubstTyping sub_id (eextend t' g) (eextend t g)
(fun x -> match x with
      | 0 -> let ht : typing (eextend t g) (EVar 0) (tot (tesh t)) = TyVar #(eextend t g) 0 in
             let ht' : typing (eextend t g) (EVar 0) (tot (tesh t')) = TySub #(eextend t g) #(EVar 0) #(tot (tesh t)) #(tot (tesh t')) ht hsc in
	     (tsubst_with_sub_id (tesh t'); ht')
      | _ -> (tsubst_with_sub_id (Some.v (lookup_evar (eextend t' g) x)); TyVar x)
)
(fun a -> (ksubst_with_sub_id (Some.v (lookup_tvar (eextend t' g) a)); KVar a))


//}}}


opaque val skinding_trans : #g:env -> #k1:knd -> #k2:knd -> #k3:knd ->
   hsk12:skinding g k1 k2 ->
   hsk23:skinding g k2 k3 ->
   Tot(skinding g k1 k3)
(decreases %[k2])
let rec skinding_trans g k1 k2 k3 hsk12 hsk23 =
match hsk12 with
| KSubRefl #x1 #x2 hw -> hsk23
| KSubKArr #x1 #k1arg #k2arg k1body k2body hsk21arg hsk12body hwf1 ->
(
 match hsk23 with
 | KSubRefl _ -> hsk12
 | KSubKArr #x2 #x3 #k3arg _ k3body hsk32arg hsk23body _ ->
 let hsk31arg : skinding g k3arg k1arg = skinding_trans hsk32arg hsk21arg in
 let hsk12body' : skinding (textend k3arg g) k1body k2body = ksubst_with_sub_id k1body; ksubst_with_sub_id k2body; skinding_substitution sub_id hsk12body (skinding_hs #g k3arg k2arg hsk32arg) in
 let hsk13body : skinding (textend k3arg g) k1body k3body = skinding_trans #(textend k3arg g) #k1body #k2body #k3body hsk12body' hsk23body in
 KSubKArr k1body k3body hsk31arg hsk13body hwf1
)
| KSubTArr #x1 #t1 #t2 #k1body #k2body hst21 hsk12body hwf1 ->
(
 match hsk23 with
 | KSubRefl _ -> hsk12
 | KSubTArr #x2 #x3 #t3 #x4 #k3body hst32 hsk23body hwf2 ->
 (
  let hst31 : styping g t3 t1 = SubTrans hst32 hst21 in
  let hsk12body' : skinding (eextend t3 g) k1body k2body = ksubst_with_sub_id k1body; ksubst_with_sub_id k2body; skinding_substitution (sub_id) hsk12body (styping_hs t3 t2 hst32) in
  let hsk13body : skinding (eextend t3 g) k1body k3body = skinding_trans #(eextend t3 g) #k1body #k2body #k3body hsk12body' hsk23body in
  KSubTArr hst31 hsk13body hwf1
 )

)


type inversion_ttapp_res : env -> typ -> typ -> knd -> Type =
| InversionTTApp : #g:env -> #t1:typ -> #t2:typ -> #kres:knd ->
  k1:knd -> k2:knd ->
  hkt1:kinding g t1 (KKArr k1 k2) ->
  hkt2:kinding g t2 k1 ->
  hsk:skinding g (ksubst_tbeta t2 k2) kres ->
  inversion_ttapp_res g t1 t2 kres

opaque val inversion_ttapp : #g:env -> #t1:typ -> #t2:typ -> #kres:knd ->
    hk : kinding g (TTApp t1 t2) kres ->
    Tot( inversion_ttapp_res g t1 t2 kres )
(decreases %[hk])
let rec inversion_ttapp g t1 t2 kres hk =
match hk with
| KTApp #x1 #x2 #x3 #k k' hkt1 hkt2 hw ->
(
 InversionTTApp k k' hkt1 hkt2 (KSubRefl #g #kres hw)
)
| KSub #x1 #x2 #k' #x3 hk hs ->
(
 let InversionTTApp k1 k2 hkt1 hkt2 hsk = inversion_ttapp #g #t1 #t2 #k' hk in
 let hsktrans = skinding_trans #g #(ksubst_tbeta t2 k2) #k' #kres hsk hs in
 InversionTTApp k1 k2 hkt1 hkt2 hsktrans
)

type inversion_teapp_res : env -> typ -> exp -> knd -> Type =
| InversionTEApp : #g:env -> #t:typ -> #e:exp -> #kres:knd ->
  targ:typ -> kbody:knd ->
  hkt: kinding g t (KTArr targ kbody) ->
  hte: typing g e (tot targ) ->
  hsk:skinding g (ksubst_ebeta e kbody) kres ->
  inversion_teapp_res g t e kres

opaque val inversion_teapp : #g:env -> #t:typ -> #e:exp -> #kres:knd ->
    hk : kinding g (TEApp t e) kres ->
    Tot (inversion_teapp_res g t e kres)
(decreases %[hk])
let rec inversion_teapp g t e kres hk =
match hk with
| KEApp #x1 #x2 #targ #kbody #x3 hkt hte hkwf ->
(
 InversionTEApp targ kbody hkt hte (KSubRefl #g #kres hkwf)
)
| KSub #x1 #x2 #k' #x3 hk' hs ->
(
 let InversionTEApp targ kbody hkt hke hsk = inversion_teapp #g #t #e #k' hk' in
 let hsktrans = skinding_trans #g #(ksubst_ebeta e kbody) #k' #kres hsk hs in
 InversionTEApp targ kbody hkt hke hsktrans
)

type inversion_telam_res : env -> typ -> typ -> knd -> Type =
| InversionTELam : #g:env -> #targ:typ -> #tbody:typ -> #ks:knd ->
        kbodyb:knd ->
        hktarg : kinding g targ KType ->
        hktbody : kinding (eextend targ g) tbody kbodyb ->
        hsk:option (skinding g (KTArr targ kbodyb) ks){KTArr targ kbodyb <> ks ==> is_Some hsk} ->
	(* SF : option only here, otherwise we need ewf of the environment … *)
        inversion_telam_res g targ tbody ks

opaque val inversion_telam : #g:env -> #targ:typ -> #tbody:typ -> #ks:knd ->
     hk:kinding g (TELam targ tbody) ks ->
     Tot( inversion_telam_res g targ tbody ks)
(decreases %[hk])
let rec inversion_telam g targ tbody ks hk =
match hk with
| KELam #g #t1 #t2 #k2 hktarg hktbody ->
(
 InversionTELam #g #targ #tbody #(KTArr targ k2) k2 hktarg hktbody None
)
| KSub #x1 #x2 #ks' #x3 hk' hsk ->
(
 let InversionTELam kbodyb ktarg hktbody hsko = inversion_telam #g #targ #tbody #ks' hk' in
 match hsko with
 | Some hskb -> (let hsk = skinding_trans #g #(KTArr targ kbodyb) #ks' #ks hskb hsk in InversionTELam #g #targ #tbody #ks kbodyb ktarg hktbody (Some hsk )
)
 | None -> InversionTELam #g #targ #tbody #ks kbodyb ktarg hktbody (Some hsk)
 )

type inversion_ttlam_res : env -> knd -> typ -> knd -> Type =
| InversionTTLam : #g:env -> #karg:knd -> #tbody:typ -> #ks:knd ->
        kbodyb:knd ->
        hkwfkarg : kwf g karg ->
        hktbody : kinding (textend karg g) tbody kbodyb ->
        hsk:option (skinding g (KKArr karg kbodyb) ks){KKArr karg kbodyb <> ks ==> is_Some hsk} ->
        inversion_ttlam_res g karg tbody ks

opaque val inversion_ttlam : #g:env -> #karg:knd -> #tbody:typ -> #ks:knd ->
     hk:kinding g (TTLam karg tbody) ks ->
     Tot( inversion_ttlam_res g karg tbody ks)
(decreases %[hk])
let rec inversion_ttlam g karg tbody ks hk =
admit()
  (* SF : the same than telam *)

opaque val kwf_tconsts : #g:env -> #tc:tconst ->
  tcwf g tc ->
  Tot (kwf g (tconsts tc))
let kwf_tconsts g tc htcwf = admit()

opaque val inversion_tconst : #g:env -> #tc:tconst -> #kres:knd ->
   hk:kinding g (TConst tc) kres ->
   Tot (skinding g (tconsts tc) kres)
(decreases %[hk])
let rec inversion_tconst g tc kres hk =
match hk with
| KConst htcwf -> KSubRefl (kwf_tconsts htcwf)
| KSub #x1 #x2 #k' hk hsk ->
(
 let hsk1 : skinding g (tconsts tc) k' = inversion_tconst hk in
 let hsk : skinding g (tconsts tc) kres = skinding_trans hsk1 hsk in
 hsk
)

type kkarr_to_kkarr_res : env -> knd -> knd -> knd -> Type =
| KKArrToKKArr : #g:env -> #karg1:knd -> #kbody1:knd -> k2:knd ->
   karg2:knd -> kbody2:knd{k2 = KKArr karg2 kbody2} ->
   hskarg : skinding g karg2 karg1 ->
   hskbody : skinding (textend karg2 g) kbody1 kbody2 ->
   kkarr_to_kkarr_res g karg1 kbody1 k2

opaque val kkarr_to_kkarr : #g:env -> #karg1:knd -> #kbody1:knd -> #k2:knd ->
   hsk:skinding g (KKArr karg1 kbody1) k2 ->
   Tot (kkarr_to_kkarr_res g karg1 kbody1 k2)

let kkarr_to_kkarr g karg1 kbody1 k2 hsk =
match hsk with
| KSubRefl hw -> let WfKArr hkwkarg hkwkbody = hw in
   KKArrToKKArr (KKArr karg1 kbody1) karg1 kbody1 (KSubRefl hkwkarg) (KSubRefl hkwkbody)
| KSubKArr #x1 #x2 #karg2 _ kbody2 hs21arg hs12body hkw ->
   KKArrToKKArr (KKArr karg2 kbody2) karg2 kbody2 hs21arg hs12body


opaque val inversion_teqt : #g:env -> t1:typ -> t2:typ -> k:knd ->
  kinding g (teqt k t1 t2) KType ->
  Tot( cand (kinding g t1 k) (kinding g t2 k))
let inversion_teqt g t1 t2 k hk =
let InversionTTApp karg2 kbody2 hkteqt1 hkt2 hsk2 = inversion_ttapp #g #(TTApp (TConst (TcEqT k)) t1) #t2 #KType hk in
let InversionTTApp karg1 kbody1 hkteq hkt1 hsk1 = inversion_ttapp #g #(TConst (TcEqT k)) #t1 #(KKArr karg2 kbody2) hkteqt1 in
let hskbase : skinding g (KKArr k (KKArr (ktsh k) KType)) (KKArr karg1 kbody1) = inversion_tconst #g #(TcEqT k) #(KKArr karg1 kbody1) hkteq in
let KKArrToKKArr x4 x5 x6 hs1arg hs1body = kkarr_to_kkarr #g #k #(KKArr (ktsh k) KType) #(KKArr karg1 kbody1) hskbase in
let hk1final : kinding g t1 k = KSub #g #t1 #karg1 #k hkt1 hs1arg in
let hs1body : skinding (textend karg1 g) (KKArr (ktsh k) KType) (kbody1) = hs1body in
let hsk2 : skinding g (KKArr k KType) (ksubst_tbeta t1 kbody1) = ksubst_tbeta_shift t1 k; skinding_substitution (sub_tbeta t1) hs1body (tbeta_hs hkt1) in
let hsk2': skinding g (KKArr k KType) (KKArr karg2 kbody2) = skinding_trans hsk2 hsk1 in
let KKArrToKKArr #x1 #x2 #x3 x4 x5 x6 hs2arg _ = kkarr_to_kkarr #g #k #KType hsk2' in
let hk2final : kinding g t2 k = KSub #g #t2 #karg2 #k hkt2 hs2arg in
Conj hk1final hk2final

opaque val inversion_teqtype : #g:env -> t1:typ -> t2:typ ->
  kinding g (teqtype t1 t2) KType ->
  Tot( cand (kinding g t1 KType) (kinding g t2 KType))
let inversion_teqtype g t1 t2 hk =
inversion_teqt t1 t2 KType hk

opaque val inversion_tand : #g:env -> t1:typ -> t2:typ ->
  kinding g (tand t1 t2) KType ->
  Tot (cand (kinding g t1 KType) (kinding g t2 KType))
let inversion_tand g t1 t2 hk =
let InversionTTApp karg2 kbody2 hktand1 hkt2 hsk2 = inversion_ttapp #g #(TTApp (TConst TcAnd) t1) #t2 #KType hk in
let InversionTTApp karg1 kbody1 hktand hkt1 hsk1 = inversion_ttapp #g #(TConst TcAnd) #t1 #(KKArr karg2 kbody2) hktand1 in
let hskbase : skinding g (KKArr KType (KKArr KType KType)) (KKArr karg1 kbody1) = inversion_tconst #g #TcAnd #(KKArr karg1 kbody1) hktand in
let KKArrToKKArr x4 x5 x6 hs1arg hs1body = kkarr_to_kkarr #g #KType #(KKArr KType KType) #(KKArr karg1 kbody1) hskbase in
let hk1final : kinding g t1 KType = KSub #g #t1 #karg1 #KType hkt1 hs1arg in
let hs1body : skinding (textend karg1 g) (KKArr KType KType) (kbody1) = hs1body in
let hsk2 : skinding g (KKArr KType KType) (ksubst_tbeta t1 kbody1) = skinding_substitution (sub_tbeta t1) hs1body (tbeta_hs hkt1) in
let hsk2': skinding g (KKArr KType KType) (KKArr karg2 kbody2) = skinding_trans hsk2 hsk1 in
let KKArrToKKArr #x1 #x2 #x3 x4 x5 x6 hs2arg _ = kkarr_to_kkarr #g #KType #KType hsk2' in
let hk2final : kinding g t2 KType = KSub #g #t2 #karg2 #KType hkt2 hs2arg in
Conj hk1final hk2final


opaque val kwf_post_pure : #g:env -> #t:typ ->
  kinding g t KType ->
  Tot (kwf g (k_post_pure t))
let kwf_post_pure g t hk = admit()

opaque val inversion_tforalle : #g:env -> t:typ -> phi:typ ->
      hk:kinding g (tforalle t phi) KType ->
      Tot (cand (kinding g t KType) (kinding (eextend t g) phi KType))
let inversion_tforalle g t phi hk = admit()

opaque val inversion_tforallt : #g:env -> k:knd -> phi:typ ->
      hk:kinding g (tforallt k phi) KType ->
      Tot (cand (kwf g k) (kinding (textend k g) phi KType))
let inversion_tforallt g k phi hk = admit()


opaque val kdg_teqe : #g:env -> #e1:exp -> #e2:exp -> #t:typ ->
               hk : kinding g t KType ->
	       ht1: typing g e1 (tot t) ->
	       ht2: typing g e2 (tot t) ->
	       Tot (kinding g (teqe t e1 e2) KType)
let kdg_teqe g e1 e2 t hk ht1 ht2 = admit()

opaque val kdg_teqt : #g:env -> #t1:typ -> #t2:typ -> #k:knd ->
               hkwf: kwf g k ->
	       hk1 : kinding g t1 k ->
	       hk2 : kinding g t2 k ->
	       Tot (kinding g (teqt k t1 t2) KType)
let kdg_teqt g t1 t2 k hkwf hk1 hk2 = admit()

opaque val kdg_tforalle : #g:env -> #t:typ -> #phi:typ ->
               hkt:kinding g t KType ->
	       hkphi:kinding (eextend t g) phi KType ->
	       Tot (kinding g (tforalle t phi) KType)
let kdg_tforalle g t phi hkt hkphi = admit()

opaque val kdg_tforallt : #g:env -> #k:knd -> #phi:typ ->
               hkwf : kwf g k ->
	       hkphi : kinding (textend k g) phi KType ->
	       Tot (kinding g (tforallt k phi) KType)
let kdg_tforallt g k phi hkwf hkphi = admit()

opaque val kdg_tand : #g:env -> #p1:typ -> #p2:typ ->
               hk1 : kinding g p1 KType ->
	       hk2 : kinding g p2 KType ->
	       Tot (kinding g (tand p1 p2) KType)
let kdg_tand g p1 p2 hk1 hk2 = admit()

opaque val kdg_tor : #g:env -> #p1:typ -> #p2:typ ->
              hk1 : kinding g p1 KType ->
	      hk2 : kinding g p2 KType ->
	      Tot (kinding g (tor p1 p2) KType)
let kdg_tor g p1 p2 hk1 hk2 = admit()

opaque val kdg_tnot : #g:env -> #t:typ ->
              hk : kinding g t KType ->
	      Tot (kinding g (tnot t) KType)
let kdg_tnot g t hk = admit()


opaque val validity_derived : #g:env -> #t:typ ->
                       hwf:ewf g ->
		       hv:validity g t ->
		       Tot (kinding g t KType)
(decreases %[hv])
let rec validity_derived g t hwf hv =
match hv with
(*| VAssume #g e t h -> admit()*)
| VRedE #g #e #t #e' ht ht' hst ->
(
 let TypingDerived hk _ _ = typing_derived #g #e #EfPure #t #(tot_wp t) hwf ht in
 kdg_teqe #g #e #e' #t hk ht ht'
)
| VEqReflE #g #e #t ht ->
(
 let TypingDerived hk _ _ = typing_derived #g #e #EfPure #t #(tot_wp t) hwf ht in
 kdg_teqe hk ht ht
)
| VSubstE #g #e1 #e2 #t' t hv12 ht1 ht2 hk hvsub ->
(
 let hs:subst_typing (sub_ebeta e2) (eextend t' g) g = ebeta_hs ht2 in
 kinding_substitution (sub_ebeta e2) hk hs
)
| VRedT #g #t #t' #k hk hk' hst ->
(
 let hkwf : kwf g k = kinding_derived hwf hk in
 kdg_teqt hkwf hk hk'
)
| VEqReflT #g #t #k hk ->
(
 let hkwf : kwf g k = kinding_derived hwf hk in
 kdg_teqt hkwf hk hk
)
| VSubstT #g #t1 #t2 #k t hv12 hkw hk hvsub ->
(
 let hkteq : kinding g (teqt k t1 t2) KType = validity_derived hwf hv12 in
 let Conj hkt1 hkt2 : cand (kinding g t1 k) (kinding g t2 k) = inversion_teqt t1 t2 k hkteq in
 let hs:subst_typing (sub_tbeta t2) (textend k g) g = tbeta_hs hkt2 in
 kinding_substitution (sub_tbeta t2) hk hs
)
| VSelAsHeap #g #h #l hth htl -> admit()
| VUpdAsHeap #g #h #l #i hth htl hti -> admit()
| VSelEq #g #eh #el #ei hth htl hti -> admit()
(* SF : ^ easy but boring *)
| VForallIntro #g #t #phi hk hv ->
(
 let hwfext = GType hwf hk in
 let hkphi : kinding (eextend t g) phi KType = validity_derived hwfext hv in
 kdg_tforalle hk hkphi
)
| VForallTypIntro #g #k #phi hkw hv ->
(
 let hwfext = GKind hwf hkw in
 let hkphi : kinding (textend k g) phi KType = validity_derived hwfext hv in
 kdg_tforallt hkw hkphi
)
| VForallElim #g #t #phi #e hv ht ->
(
 let hkforall : kinding g (tforalle t phi) KType = validity_derived hwf hv in
 let Conj hkt hkphi = inversion_tforalle t phi hkforall in
 let hs:subst_typing (sub_ebeta e) (eextend t g) g = ebeta_hs ht in
 kinding_substitution (sub_ebeta e) hkphi hs
)
| VForallTypElim #g #t #k #phi hv hk ->
(
 let hkforall : kinding g (tforallt k phi) KType = validity_derived hwf hv in
 let Conj hkwf hkphi = inversion_tforallt k phi hkforall in
 let hs:subst_typing (sub_tbeta t) (textend k g) g = tbeta_hs hk in
 kinding_substitution (sub_tbeta t) hkphi hs
)
| VAndElim1 #g #p1 #p2 hv ->
(
 let hkand : kinding g (tand p1 p2) KType = validity_derived hwf hv in
 let Conj hkp1 hkp2 = inversion_tand p1 p2 hkand in
 hkp1
)
| VAndElim2 #g #p1 #p2 hv ->
(
 let hkand : kinding g (tand p1 p2) KType = validity_derived hwf hv in
 let Conj hkp1 hkp2 = inversion_tand p1 p2 hkand in
 hkp2
)
| VAndIntro #g #p1 #p2 hv1 hv2 ->
(
 let hk1 = validity_derived hwf hv1 in
 let hk2 = validity_derived hwf hv2 in
 kdg_tand hk1 hk2
)
| VExMiddle #g #t1 #t2 hk1 hk2 hv1 hv2 -> hk2
| VOrIntro1 #g #t1 #t2 hv hk ->
(
 let hk1 : kinding g t1 KType = validity_derived hwf hv in
 kdg_tor hk1 hk
)
| VOrIntro2 #g #t1 #t2 hv hk ->
(
 let hk2 : kinding g t2 KType = validity_derived hwf hv in
 kdg_tor hk hk2
)
| VOrElim #g #t1 #t2 #t3 hk1 hk2 hk3 hvor hv1 hv2 -> hk3
| VFalseElim #g #t hv hk -> hk
| VPreceedsIntro #g #v1 #v2 #t1 #t2 ht1 ht2 -> admit()
(* SF : problem in spec here : kinding problem *)
| VDistinctC #g #t #c1 #c2 ht1 ht2 ->
(
 let TypingDerived hkt _ _ = typing_derived #g #(EConst c1) #EfPure #t #(tot_wp t) hwf ht1 in
 let hkteqe : kinding g (teqe t (EConst c1) (EConst c2)) KType = kdg_teqe hkt ht1 ht2 in
 kdg_tnot hkteqe
)
| VDistinctTH #g #t1 #t2 hk1 hk2 ->
(
 let hkteqtype : kinding g (teqtype t1 t2) KType = kdg_teqt (WfType g) hk1 hk2 in
 kdg_tnot hkteqtype
)
| VInjTH #g #t1 #t2 #phi #t1' #t2' #phi' #m hvtemp ->
(
 let hk : kinding g (teqtype (TArr t1  (Cmp m t2  phi)) (TArr t1' (Cmp m t2' phi')) ) KType = validity_derived hwf hvtemp in
 let Conj hkarr hkarr' : cand (kinding g (TArr t1 (Cmp m t2 phi)) KType) (kinding g (TArr t1' (Cmp m t2' phi')) KType) = inversion_teqtype (TArr t1 (Cmp m t2 phi)) (TArr t1' (Cmp m t2' phi')) hk in
 let InversionTArr hkt1 hkt2 hkphi _ = inversion_tarr #g #t1 #m #t2 #phi hkarr in
 let InversionTArr hkt1' hkt2' hkphi' _ = inversion_tarr #g #t1' #m #t2' #phi' hkarr' in
 let hvtemp1 : validity g (tand (teqtype t1 t1') (tforalle t1 (teqtype t2 t2'))) = VAndElim1 #g #(tand (teqtype t1 t1') (tforalle t1 (teqtype t2 t2'))) #(tforalle t1 (teqt (k_m m t2) phi phi')) hv in
 let hveqt1 : validity g (teqtype t1 t1') = VAndElim1 #g #(teqtype t1 t1') #(tforalle t1 (teqtype t2 t2')) hvtemp1 in
 let hst1 : styping g t1 t1' = SubConv t1 hveqt1 hkt1' hkt1 in
 let hs : subst_typing (sub_id) (eextend t1' g) (eextend t1 g) = styping_hs t1 t1' hst1 in
 let hkt2' : kinding (eextend t1 g) t2' KType = tsubst_with_sub_id t2'; kinding_substitution (sub_id) hkt2' hs in
 let hkphi' : kinding (eextend t1 g) phi' (k_m m t2') = tsubst_with_sub_id phi'; ksubst_with_sub_id (k_m m t2'); kinding_substitution (sub_id) hkphi' hs in
 let hkteqt2 : kinding (eextend t1 g) (teqtype t2 t2') KType = kdg_teqt (WfType (eextend t1 g)) hkt2 hkt2' in
 let hkteqphi : kinding (eextend t1 g) (teqt (k_m m t2) phi phi') KType = magic() in
 admit()
(* SF : problem : I need kinding (eextend t1 g) phi' (k_m m t2) *)
)
| _ -> admit()

//{{{
opaque val op_pure_timpl : g:env -> t:typ -> wp1:typ -> wp2:typ ->
     validity (textend (k_post_pure t) g) (timpl (TTApp (wp1) (TVar 0)) (TTApp (wp2) (TVar 0))) ->
     Tot (validity (textend (k_post_pure t) g) (TTApp (op EfPure (ttsh t) timpl wp1 wp2) (TVar 0)))
let op_pure_timpl g t wp1 wp2 hv =
admit()


let ret_weakest e m t wp =
down m t (op m t timpl wp (lift EfPure m t (return_pure t e)))


opaque val tot_ret_weakest : #g:env -> #e:exp -> #t:typ ->
                      hwf:ewf g ->
                      ht: typing g e (tot t) ->
                      Tot (validity g (ret_weakest e EfPure t (tot_wp t)))
let tot_ret_weakest g e t hwf ht = admit()
  (*{{{
let TypingDerived hk kwp _ = typing_derived hwf ht in
let wp = tot_wp t in
let g' = textend (k_post_pure t) g in
let wpp = TTApp (ttsh wp) (TVar 0) in
let kwp' : kinding g' (ttsh wp) (k_m EfPure (ttsh t)) = (*kinding_substitution sub_tinc kwp (hs_sub_tinc g (k_post_pure t))*) magic() in
let hkwpp : kinding g' wpp KType = KTApp KType kwp' (KVar 0) (WfType g') in
let hkwf : kwf g (k_post_pure t) = magic() (*KTApp KType*)  in
let g'' = eextend (wpp) g' in
let rhs = (TTApp (ttsh (return_pure t e)) (TVar 0)) in
let hv1 : validity g'' (tesh rhs) =
begin
  let hv: validity g'' (TTApp (tot_wp (tesh (ttsh t))) (TVar 0)) = magic() in
  let ht' : typing g' (etsh e) (tot (ttsh t)) = subst_on_tot sub_tinc t; typing_substitution (sub_tinc) ht (hs_sub_tinc g (k_post_pure t)) in
  let ht'' : typing g'' (eesh (etsh e)) (tot (tesh (ttsh t))) = subst_on_tot sub_einc (ttsh t); typing_substitution (sub_einc) ht' (hs_sub_einc g' wpp) in
  let hk1 : kinding g'' (TTApp (tot_wp (tesh (ttsh t))) (TVar 0)) KType = magic() in
  let hk2 : kinding g'' (tforalle (tesh (ttsh t)) (TEApp (TVar 0) (EVar 0))) KType = magic() in
  let hv'' : validity g'' (teqt KType (TTApp (tot_wp (tesh (ttsh t))) (TVar 0)) (tforalle (tesh (ttsh t)) (TEApp (TVar 0) (EVar 0)))) = magic() in
  let hv'' : validity g'' (tforalle (tesh (ttsh t)) (TEApp (TVar 0) (EVar 0))) = magic() in
  let hv'' : validity g'' (TEApp (TVar 0) (eesh (etsh e))) = VForallElim hv'' ht'' in
  let hv'' : validity g'' (tesh (TEApp (TVar 0) (etsh e))) = hv'' in
  let hv'' : validity g'' (tesh (TTApp ((TTLam (k_post_pure (ttsh t)) (TEApp (TVar 0) (etsh (etsh e))))) (TVar 0))) = magic() in
  let hv'' : validity g'' (tesh (TTApp (ttsh (TTLam (k_post_pure t) (TEApp (TVar 0) (etsh e)))) (TVar 0))) = magic() in
  let hv'' : validity g'' (tesh (TTApp (ttsh (return_pure t e)) (TVar 0))) = magic() in
  hv''
  (*SF : need to deal here with substitution with equal types.
   It is going to be hard …*)
end
in
let hvimpl : validity g' (timpl wpp rhs) = v_impl_intro wpp rhs hkwpp hv1 in
let hvimpl' : validity g' (TTApp (ttsh (op EfPure (t) timpl (wp) ((return_pure t e)))) (TVar 0)) = subst_on_op_timpl sub_tinc EfPure t wp (return_pure t e); op_pure_timpl g (t) (ttsh wp) (ttsh (return_pure t e)) hvimpl in
let hvimpl'' : validity g (down_pure t (op EfPure t timpl wp (return_pure t e))) = VForallTypIntro hkwf hvimpl' in
hvimpl''
}}}*)
(* SF : ^ this part does not work anymore … out of nowhere *)


opaque val sc_tot : #g:env -> #t':typ -> #t:typ ->
             hst:styping g t' t ->
	     Tot (scmp g (tot t') (tot t))
let sc_tot g t' t hst = admit()

(* SF : the TyApp case is going to be complicated … *)


type styping_inv_arr_res : env -> typ -> cmp -> typ -> Type =
| StypingInvArr : #g:env -> #t1:typ -> #c1:cmp -> #t:typ ->
                t2:typ -> c2:cmp{t = TArr t2 c2} ->
                styping g t2 t1 ->
                scmp (eextend t2 g) c1 c2 ->
                styping_inv_arr_res g t1 c1 t

opaque val styping_inversion_arrow : #g:env -> #t1:typ -> #c1:cmp -> #t:typ ->
    hwf:ewf g ->
    hst:styping g (TArr t1 c1) t ->
    Tot(either (styping_inv_arr_res g t1 c1 t) (validity g tfalse))
(decreases %[hst])
let rec styping_inversion_arrow g t1 c1 t hwf hst = admit()
  (*
match hst with
| SubFun #g #t2 #t1 #c1 #c2 hst hk hsc ->
(
 Inl (StypingInvArr t2 c2 hst hsc)
)
| SubConv #g #t t' hv hk ->
(
 let Cmp mc1 tc1 wp1 = c1 in
 if not (is_TArr t) then
  admit()
 else
   if true then
   admit()
   (*
     let hktarr1 : kinding g (TArr t1 c1) KType = magic() in (*How do I get this ???*)
     let hktarr2 : kinding g (TArr t2 c2) KType = styping_derived hst in
     let hvimpl : validity g (tnot (teqtype (TArr t1 c1) (TArr t2 c2))) = VDistinctTH hktarr1 hktarr2 in
     let hvfalse : validity g tfalse = v_impl_elim hvimpl hv in
     Inr (hvfalse)
     (*in order to apply VDistinctTH, I need a kinding proof for TArr t2 c2 …*)
     *)
   else
     admit()
)
| SubTrans #g #t1 #t2 #t3 hs12 hs23 ->
(
(*
 match (styping_inversion_arrow hwf hs12) with
 | Inr hv -> Inr hv
 | Inl h1 ->
 (
  let Conj hst21 hscmp12 = h1 in
  match (styping_inversion_arrow hwf hs23) with
  | Inr hv -> Inr hv
  | Inl h2 ->
  (
   let Conj hst32 hscmp23 = h2 in
   admit()
  )
 )
*)
admit()
)
| _ -> admit()
  *)

type stypingd_inv_arr_res : env -> typ -> typ -> cmp -> Type =
| StypingDInvArr : #g:env -> #t:typ -> #t2:typ -> #c2:cmp ->
                t1:typ -> c1:cmp{t = TArr t1 c1} ->
                styping g t2 t1 ->
                scmp (eextend t2 g) c1 c2 ->
                stypingd_inv_arr_res g t t2 c2

opaque val stypingd_inversion_arrow : #g:env -> #t:typ -> #t2:typ -> #c2:cmp ->
    hwf:ewf g ->
    hst:styping g t (TArr t2 c2)->
    Tot(either (stypingd_inv_arr_res g t t2 c2) (validity g tfalse))
(decreases %[hst])
let rec stypingd_inversion_arrow g t t2 c2 hwf hst = admit()

opaque val scmp_transitivity : #g:env -> #c1:cmp -> #c2:cmp -> #c3:cmp ->
                        scmp g c1 c2 ->
			scmp g c2 c3 ->
			Tot (scmp g c1 c3)
let scmp_transitivity g c1 c2 c3 hs12 hs23 =
let Cmp m1 t1 wp1 = c1 in
let Cmp m2 t2 wp2 = c2 in
let Cmp m3 t3 wp3 = c3 in
let SCmp _ _ _ _ hst12 hkwp2 hvmono2 hkwp1 hvmono1 hvsub12 = hs12 in
let SCmp _ _ _ _ hst23 hkwp3 hvmono3 hkwp2 hvmono2 hvsub23 = hs23 in
let hst13 = SubTrans hst12 hst23 in
let hvsub13 : validity g (sub_computation m3 t3 wp3 m1 t1 wp1) =
  admit() (*TODO:fill this*)
in
SCmp #g m1 #t1 wp1 m3 #t3 wp3 hst13 hkwp3 hvmono3 hkwp1 hvmono1 hvsub13
(* SF : ^ still not up-to-date since the changes on scmp *)

opaque val styping_refl : #g:env -> #t:typ ->
      kinding g t KType ->
      Tot (styping g t t)
let styping_refl g t hk =
  let hv : validity g (teqtype t t) = VEqReflT #g #t #KType hk in
  SubConv #g #t t hv hk hk

opaque val scmp_refl : #g:env -> #m:eff -> #t:typ -> #wp:typ ->
     hkt : kinding g t KType ->
     hkwp : kinding g wp (k_m m t) ->
     hvmono : validity g (monotonic m t wp) ->
     Tot (scmp g (Cmp m t wp) (Cmp m t wp))
let scmp_refl g m t wp hkt hkwp hvmono =
  let hvsub : validity g (sub_computation m t wp m t wp) = magic() in
  SCmp #g m #t wp m #t wp (styping_refl #g #t hkt) hkwp hvmono hkwp hvmono hvsub

type styping_arrow_to_arrow_res : env -> typ -> cmp -> typ -> Type =
| StypingAToA : #g:env -> #t1:typ -> #c1:cmp -> #t:typ ->
    #t1':typ -> #c1':cmp ->
    validity g (teqtype t (TArr t1' c1')) ->
    styping g t1' t1 ->
    scmp (eextend t1' g) c1 c1' ->
    styping_arrow_to_arrow_res g t1 c1 t

opaque val styping_arrow_to_arrow : #g:env -> #t1:typ -> #c1:cmp -> #s:typ -> #t:typ ->
  hwf : ewf g ->
  hv:validity g (teqtype s (TArr t1 c1)) ->
  hst:styping g s t ->
  Tot(either (styping_arrow_to_arrow_res g t1 c1 t) (validity g tfalse))
(decreases %[hst])
let rec styping_arrow_to_arrow g t1 c1 s t hwf hv hst =
admit()(*
match hst with
| SubConv _ hvseqt hkt hks ->
(
 (* s =_Type t and s =_Type TArr t1 c1*)
 let hkv : kinding g (teqtype s (TArr t1 c1)) KType = validity_derived #g #(teqtype s (TArr t1 c1)) hwf hv in
 let Conj _ hk = inversion_teqtype #g #s #(TArr t1 c1) hkv in
 let hv' : validity g (teqtype t (TArr t1 c1)) = let hvteqs : validity g (teqtype t s) = v_eq_symt #g #s #t #KType hvseqt in v_eq_trant #g #t #s #(TArr t1 c1) #KType hvteqs hv(*transitivity*) in
 let Cmp m1 tret1 wp1 = c1 in
 let InversionTArr #g #t1 hkt1 hktret1 hkwp1 hvmono1 = inversion_tarr #g #t1 #m1 #tret1 #wp1 hk in
 let hst' : styping g t1 t1 = styping_refl #g #t1 hkt1 in
 let hscmp' : scmp (eextend t1 g) c1 c1 = scmp_refl #(eextend t1 g) #m1 #tret1 #wp1 hktret1 hkwp1 hvmono1 in
 Inl (StypingAToA #g #t1 #c1 #t #t1 #c1 hv' hst' hscmp')
)
| SubFun #g #tt #st #sc #tc hsttarg hscmp hk' ->
(
 (* s = TArr st sc, t = TArr tt tc *)
 (* s =_Type TArr t1 c1 *)
 (* g |- tt <: st *)
 (* g,tt |- sc <: tc *)
 let hkv : kinding g (teqtype s (TArr t1 c1)) KType = validity_derived #g #(teqtype s (TArr t1 c1)) hwf hv in
 let Conj _ hk = inversion_teqtype #g #s #(TArr t1 c1) hkv in
 let Conj hks hkt = styping_derived hst in
 if Cmp.m c1 <> Cmp.m sc then
   let hvnoteq : validity g (tnot (teqtype s (TArr t1 c1))) = VDistinctTH #g #s #(TArr t1 c1) hks hk in
   let hvfalse : validity g tfalse = v_impl_elim hvnoteq hv in
   Inr hvfalse
 else
   let Cmp m tret1 wp1 = c1 in
   let Cmp m stret swp = sc in
   let hv3 : validity g (tand (tand (teqtype st t1) (tforalle st (teqtype stret tret1))) (tforalle st (teqt (k_m m stret) swp wp1))) = VInjTH #g #st #stret #swp #t1 #tret1 #wp1 #m hv in
   let hv2 : validity g (tand (teqtype st t1) (tforalle st (teqtype stret tret1))) = VAndElim1 #g #(tand (teqtype st t1) (tforalle st (teqtype stret tret1))) #(tforalle st (teqt (k_m m stret) swp wp1)) hv3 in
   let hveqwp : validity g (tforalle st (teqt (k_m m stret) swp wp1)) = VAndElim2 #g #(tand (teqtype st t1) (tforalle st (teqtype stret tret1))) #(tforalle st (teqt (k_m m stret) swp wp1)) hv3 in
   let hveqtarg : validity g (teqtype st t1) = VAndElim1 #g #(teqtype st t1) #(tforalle st (teqtype stret tret1)) hv2 in
   let hveqtret : validity g (tforalle st (teqtype stret tret1)) = VAndElim2 #g #(teqtype st t1) #(tforalle st (teqtype stret tret1)) hv2 in
   let InversionTArr hkst hkstret hkswp hvmonoswp = inversion_tarr #g #st #m #stret #swp hks in
   let InversionTArr hkt1 hktret1 hkwp1 hvmonowp1 = inversion_tarr #g #t1 #m #tret1 #wp1 hk in
   let hveqt : validity g (teqtype t t) = VEqReflT #g #t #KType hkt in
   let hststt1 : styping g st t1 = SubConv #g #t1 #st hveqtarg hkt1 hkst in
   let hstttt1 : styping g tt t1 = SubTrans #g #tt #st #t1 hsttarg hststt1 in
   let hscc1tc : scmp (eextend tt g) c1 tc = admit() (*hs : SubConv on hveqtret and SubTrans, hk : inversion on hscmp, hvmono : inversion on scmp, hk': inversion on hk', hvmono' : stronger inversion on hk', hvsub : use the teqtype between s and TArr t1 c1 to get what you want*)
   in
   Inl (StypingAToA #g #t1 #c1 #t #tt #tc hveqt hstttt1 hscc1tc)
)
| SubTrans #g #s #u #t hssu hsut ->
(
  let temp : either (styping_arrow_to_arrow_res g t1 c1 u) (validity g tfalse) = styping_arrow_to_arrow hwf hv hssu in
  if (is_Inr temp) then Inr (Inr.v temp) else

  let StypingAToA #x1 #x2 #x3 #x4 #ut #uc hvtequ hstutt1 hscc1uc : styping_arrow_to_arrow_res g t1 c1 u = Inl.v temp in
  let temp : either (styping_arrow_to_arrow_res g ut uc t) (validity g tfalse) = styping_arrow_to_arrow hwf hvtequ hsut in
  if (is_Inr temp) then Inr (Inr.v temp) else
  let StypingAToA #x5 #x6 #x7 #x8 #tt #tc hvteqt hstttut hscuctc : styping_arrow_to_arrow_res g ut uc t = Inl.v (temp) in (* needs g |- TArr ut uc : KType *)
  let hstttt1 : styping g tt t1 = SubTrans #g #tt #ut #t1 hstttut hstutt1 in
  let hs : subst_typing sub_id (eextend ut g) (eextend tt g) = styping_hs tt ut hstttut in
  let hscc1uc' : scmp (eextend tt g) c1 uc = csubst_with_sub_id c1; csubst_with_sub_id uc; scmp_substitution sub_id hscc1uc hs in
  let hscc1tc : scmp (eextend tt g) c1 tc = scmp_transitivity #(eextend tt g) #c1 #uc #tc hscc1uc' hscuctc in

  Inl (StypingAToA #g #t1 #c1 #t #tt #tc hvteqt hstttt1 hscc1tc)
)
*)

opaque val styping_inv_arr : #g:env -> #t1:typ -> #c1:cmp -> #t2:typ -> #c2:cmp -> #r1:typ -> #r2:typ ->
   hwf:ewf g ->
   hst:styping g r1 r2 ->
   hv1:validity g (teqtype r1 (TArr t1 c1)) ->
   hv2:validity g (teqtype r2 (TArr t2 c2)) ->
   Tot(either (cand (styping g t2 t1) (scmp (eextend t2 g) c1 c2))
              (validity g tfalse))
let styping_inv_arr g t1 c1 t2 c2 r1 r2 hwf hst hv1 hv2 =
admit()(*
let temp = styping_arrow_to_arrow #g #t1 #c1 #r1 #r2 hwf hv1 hst in
if is_Inr temp then Inr (Inr.v temp)
else
let StypingAToA #x1 #x2 #x3 #x4 #t1' #c1' hvr2eqt1c1' hstt1't1 hscc1c1' : styping_arrow_to_arrow_res g t1 c1 r2 = Inl.v temp in
(*hvr1eqt1c1 : r2 =_Type TArr t1' c1'
 -> TArr t1' c1' = TArr t2 c2 with hv2 *)
(*goal : t2 <: t1', c1'<:c2 *)
let hvtarr2eqtarr1' : validity g (teqtype (TArr t2 c2) (TArr t1' c1')) =
  let hvtemp1 : validity g (teqtype (TArr t2 c2) r2) = v_eq_symt #g #r2 #(TArr t2 c2) #KType hv2 in v_eq_trant #g #(TArr t2 c2) #r2 #(TArr t1' c1') #KType hvtemp1 hvr2eqt1c1' in
let Cmp m1' tret1' wp1' = c1' in
let Cmp m2 tret2 wp2 = c2 in
let hktarr1' : kinding g (TArr t1' c1') KType = magic() in
let Conj hktarr2 hktarr1' : cand (kinding g (TArr t2 c2) KType) (kinding g (TArr t1' c1') KType) = inversion_teqtype #g (TArr t2 c2) (TArr t1' c1') (validity_derived #g #(teqtype (TArr t2 c2) (TArr t1' c1')) hwf hvtarr2eqtarr1') in
if m1' <> m2 then
  let hvnot : validity g (tnot (teqtype (TArr t2 c2) (TArr t1' c1'))) = VDistinctTH #g #(TArr t2 c2) #(TArr t1' c1') hktarr2 hktarr1' in
  let hvfalse : validity g tfalse = v_impl_elim #g #(teqtype (TArr t2 c2) (TArr t1' c1')) #tfalse hvnot hvtarr2eqtarr1' in
  Inr hvfalse
else
  let hv3and : validity g (tand (tand (teqtype t2 t1') (tforalle t2 (teqtype tret2 tret1' ))) (tforalle t2 (teqt (k_m m1' (tret2)) wp2 wp1'))) = VInjTH #g #t2 #tret2 #wp2 #t1' #tret1' #wp1' #m1' hvtarr2eqtarr1' in
  let hv2and : validity g (tand (teqtype t2 t1') (tforalle t2 (teqtype tret2 tret1'))) = VAndElim1 #g #(tand (teqtype t2 t1') (tforalle t2 (teqtype tret2 tret1'))) #(tforalle t2 (teqt (k_m m1' (tret2)) wp2 wp1')) hv3and in
  let hvt2eqt1' : validity g (teqtype t2 t1') = VAndElim1 #g #(teqtype t2 t1') #(tforalle t2 (teqtype tret2 tret1')) hv2and in
  let hvtret2eqtret1' : validity g (tforalle t2 (teqtype tret2 tret1')) = VAndElim2 #g #(teqtype t2 t1') #(tforalle t2 (teqtype tret2 tret1')) hv2and in
  let hvwp2eqwp1' : validity g (tforalle t2 (teqt (k_m m1' (tret2)) wp2 wp1')) = VAndElim2 #g #(tand (teqtype t2 t1') (tforalle t2 (teqtype tret2 tret1'))) #(tforalle t2 (teqt (k_m m1' (tret2)) wp2 wp1')) hv3and in
  let InversionTArr hkt1' hktret1'ext1 hkwp1'ext1 hvmono1'ext1 = inversion_tarr #g #t1' #m1' #tret1' #wp1' hktarr1' in
  let InversionTArr hkt2  hktret2ext hkwp2ext hvmono2ext = inversion_tarr #g #t2 #m2 #tret2 #wp2 hktarr2 in
  let hstt2t1' : styping g t2 t1' = SubConv #g #t1' t2 hvt2eqt1' hkt1' hkt2 in
  (* goal : scmp (eextend t2 g) c1' c2
     -> styping (eextend t2 g) tret1' tret2
     -> kinding (eextend t2 g) wp2 (k_m m tret2)
     -> validity (eextend t2 g) (mono wp2)
     -> kinding (eextend t2 g) wp1' (k_m m tret1')
     -> validity (eextend t2 g) (mono wp1')
     -> validity sub_computation wp2 wp1'
   *)
  let gext = eextend t2 g in
  let hscc1'c2 : scmp gext c1' c2 =
    let hwfext : ewf gext = GType hwf hkt2 in
    let hveqretext : validity gext (teqtype tret2 tret1') = v_inv_foralle #g t2 (teqtype tret2 tret1') hvtret2eqtret1' in (*v_eq_symt #gext #tret2 #tret1' #KType hst in*)
    let Conj hktret2 hktret1' : cand (kinding gext tret2 KType) (kinding gext tret1' KType) = inversion_teqtype #gext #tret2 #tret1' (validity_derived #gext #(teqtype tret2 tret1') hwfext hveqretext) in
    let hstret : styping (eextend t2 g) tret1' tret2 = SubConv #gext #tret2 tret1' (v_eq_symt #gext #tret2 #tret1' #KType hveqretext) hktret2 hktret1' in
    let hkwp1'ext : kinding gext wp1' (k_m m1' tret1') = tsubst_with_sub_id wp1'; ksubst_with_sub_id (k_m m1' tret1'); kinding_substitution (sub_id) hkwp1'ext1 (styping_hs #g t2 t1' hstt2t1') in
    let hvmono1'ext : validity gext (monotonic m1' tret1' wp1') = tsubst_with_sub_id (monotonic m1' tret1' wp1'); validity_substitution (sub_id) hvmono1'ext1 (styping_hs #g t2 t1' hstt2t1') in
    let hvsubext : validity gext (sub_computation m2 tret2 wp2 m1' tret1' wp1') = magic() in
    (*^ TODO*)
    SCmp #gext m1' #tret1' wp1' m2 #tret2 wp2 hstret hkwp2ext hvmono2ext hkwp1'ext hvmono1'ext hvsubext in
  let hscc1c1' : scmp gext c1 c1' = csubst_with_sub_id c1; csubst_with_sub_id c1'; scmp_substitution (sub_id) (hscc1c1') (styping_hs #g t2 t1' hstt2t1') in
  let hscc1c2 : scmp gext c1 c2 = scmp_transitivity #gext #c1 #c1' #c2 hscc1c1' hscc1'c2 in
  let hstt2t1 : styping g t2 t1 = SubTrans #g #t2 #t1' #t1 hstt2t1' hstt1't1 in
  Inl (Conj hstt2t1 hscc1c2)
*)

opaque val styping_inv_arr' : #g:env -> #t1:typ -> #c1:cmp -> #t2:typ -> #c2:cmp ->
   hwf:ewf g ->
   hst:styping g (TArr t1 c1) (TArr t2 c2) ->
   Tot(either (cand (styping g t2 t1) (scmp (eextend t2 g) c1 c2))
              (validity g tfalse))
let styping_inv_arr' g t1 c1 t2 c2 hwf hst =
let Conj hktarr1 hktarr2 = styping_derived hst in
let hv1 : validity g (teqtype (TArr t1 c1) (TArr t1 c1)) = VEqReflT hktarr1 in
let hv2 : validity g (teqtype (TArr t2 c2) (TArr t2 c2)) = VEqReflT hktarr2 in
styping_inv_arr #g #t1 #c1 #t2 #c2 #(TArr t1 c1) #(TArr t2 c2) hwf hst hv1 hv2


type abs_inversion_res : g:env -> targ:typ -> ebody:exp -> ms:eff -> tlams:typ -> wps:typ -> Type =
| AbsInversion : #g:env -> #targ:typ -> #ebody:exp -> #ms:eff -> #tlams:typ -> #wps:typ ->
   mb:eff -> tretb:typ -> wpb:typ ->
   typing (eextend targ g) ebody (Cmp mb tretb wpb) ->
   styping g (TArr targ (Cmp mb tretb wpb)) tlams ->
   validity g (ret_weakest (ELam targ ebody) ms tlams wps) ->
   abs_inversion_res g targ ebody ms tlams wps

opaque val abs_inversion : #g:env -> #targ:typ -> #ebody:exp ->
     #ms:eff -> #tlams:typ -> #wps:typ ->
     hwf:ewf g ->
     ht:typing g (ELam targ ebody) (Cmp ms tlams wps) ->
     Tot (abs_inversion_res g targ ebody ms tlams wps)
(decreases %[ht])
let rec abs_inversion g targ ebody ms tlams wps hwf ht =
match ht with
| TyAbs mb tretb wpb hktarg htbody ->
(
 let hktarr : kinding g tlams KType = let TypingDerived hktarr _ _ = typing_derived #g #(ELam targ ebody) #ms #tlams #wps hwf ht in hktarr in
 let hveq : validity g (teqtype tlams tlams) = VEqReflT #g #tlams #KType hktarr in
 let hst : styping g tlams tlams = SubConv tlams hveq hktarr hktarr in
 let hvretweak : validity g (ret_weakest (ELam targ ebody) ms tlams wps) = admit() (* TODO : here, it is tot_wp ==> return_pure *) in
 AbsInversion #g #targ #ebody #ms #tlams #wps mb tretb wpb htbody hst hvretweak
)
| TyRet tlams htot ->
(
 let AbsInversion mb tretb wpb htbody hst _ = abs_inversion #g #targ #ebody #EfPure #tlams #(tot_wp tlams) hwf htot in
 let hvretweak : validity g (ret_weakest (ELam targ ebody) EfPure tlams (return_pure tlams (ELam targ ebody))) = magic() (* return_pure ==> return_pure … *) in
 AbsInversion #g #targ #ebody #EfPure #tlams #(return_pure tlams (ELam targ ebody)) mb tretb wpb htbody hst hvretweak
)
| TySub #x1 #x2 #c' #c htc' hsc ->
(
 let Cmp mc' tc' wpc' = c' in
 let Cmp mc tc wpc = c in
 let AbsInversion mb tretb wpb htbody hst hvretweak' = abs_inversion #g #targ #ebody #mc' #tc' #wpc' hwf htc' in
 let hst : styping g (TArr targ (Cmp mb tretb wpb)) tc =
   let hsttemp : styping g tc' tc = SCmp.hs hsc in
   SubTrans #g #(TArr targ (Cmp mb tretb wpb)) #tc' #tc hst hsttemp in
 let hvretweak : validity g (ret_weakest (ELam targ ebody) mc tc wpc) = magic() in
 AbsInversion #g #targ #ebody #mc #tc #wpc mb tretb wpb htbody hst hvretweak
)

type scmpex : env -> e:exp -> cmp -> cmp -> Type =
| SExTrans : #g:env -> #e:exp -> #c1:cmp -> #c2:cmp -> #c3:cmp ->
             scmpex g e c1 c2 ->
             scmpex g e c2 c3 ->
	     scmpex g e c1 c3
| SExSCmp : #g:env -> #e:exp -> #c1:cmp -> #c2:cmp ->
            scmp g c1 c2 ->
	    scmpex g e c1 c2
| SExRet : #g:env -> #e:exp -> #t:typ ->
           typing g e (tot t) ->
	   scmpex g e (tot t) (return_pure_cmp t e)

opaque val subtype_with_scmpex : #g:env -> #e:exp -> #c1:cmp -> #c2:cmp -> #e':exp ->
      scmpex g e c1 c2 ->
      typing g e' c1 ->
      epstep e e' ->
      Tot (typing g e' c2)
let subtype_with_scmpex g e c1 c2 e' hsc ht hstep = admit()

type remove_subtyping_res : env -> exp -> cmp -> Type =
| RemoveSub : #g:env -> #e:exp -> #c:cmp ->
  c' : cmp ->
  hsc: scmpex g e c' c ->
  ht': typing g e c'{not(is_TySub ht') /\ not(is_TyRet ht')} ->
  remove_subtyping_res g e c

opaque val remove_subtyping : #g:env -> #e:exp -> #c:cmp ->
     hwf:ewf g ->
     ht:typing g e c ->
     Tot(remove_subtyping_res g e c)
  (decreases %[ht])
let rec remove_subtyping g e c hwf ht =
if not (is_TySub ht) && not (is_TyRet ht) then
  let Cmp mc tc wpc = c in
  let TypingDerived hktc hkwpc hvmonoc = typing_derived #g #e #mc #tc #wpc hwf ht in
  let hsc : scmp g c c = scmp_refl #g #mc #tc #wpc hktc hkwpc hvmonoc in
  let hscex : scmpex g e c c = SExSCmp #g #e #c #c hsc in
  RemoveSub #g #e #c c hscex ht
else
match ht with
| TySub #x1 #x2 #c' #x4 ht' hsc ->
(
 let RemoveSub c'' hsc' ht' = remove_subtyping #g #e #c' hwf ht' in
 let hsctemp : scmpex g e c' c = SExSCmp #g #e #c' #c hsc in
 let hsc : scmpex g e c'' c = SExTrans hsc' hsctemp in
 RemoveSub #g #e #c c'' hsc ht'
)
| TyRet _ htot ->
(
 let Cmp mc tc wpc = c in
 let RemoveSub c' hsc' ht' = remove_subtyping hwf htot in
 let hscex : scmpex g e (tot tc) (return_pure_cmp tc e) = SExRet #g #e #tc htot in
 let hscex : scmpex g e c' (return_pure_cmp tc e) = SExTrans #g #e #c' #(tot tc) #(return_pure_cmp tc e) hsc' hscex in
 RemoveSub #g #e #c c' hscex ht'
)

opaque val get_styping_from_scmpex : #g:env -> #e:exp -> #c':cmp -> #c:cmp ->
   hs:scmpex g e c' c ->
   Tot (styping g (Cmp.t c') (Cmp.t c))
let get_styping_from_scmpex g e c' c hs = admit()

(*
type inversion_tot_res : g:env -> e:exp -> mb:eff -> tb:typ -> wpb:typ ->
                                           ms:eff -> ts:typ -> wps:typ ->
					   Type =
| InversionNotTot : #g:env -> #e:exp -> #mb:eff -> #tb:typ -> #wpb:typ ->
                    #ms:eff{eff_sub mb ms} -> #ts:typ -> #wps:typ ->
	            validity g (sub_computation ms ts wps mb tb wpb) ->
		    inversion_tot_res g e mb tb wpb ms ts wps
| InversionTot :    #g:env -> #e:exp -> #mb:eff{mb=EfPure} -> #tb:typ -> #wpb:typ ->
#ms:eff -> #ts:typ -> #wps:typ ->
		    validity g (sub_computation EfPure ts (tot_wp ts) EfPure tb wpb) ->
		    validity g (sub_computation ms ts wps EfPure ts (return_pure ts e)) ->
		    typing g e (tot ts) ->
		    inversion_tot_res g e mb tb wpb ms ts wps
(* SF : We could write inversion_tot_res as some kind of list to represent the T-Sub / T-Ret chain. It would be easier than trying to manipulate
 the sub_computation validity terms … *)

(*
type app_inversion_pure : g:env -> e1:exp -> e2:exp -> ms:eff -> trets:typ -> wp0:typ ->                          mb:eff -> targ:typ -> tbody:typ -> wpbody:typ -> wp1:typ -> wp2:typ -> Type =
| AppInversionPure : g:env -> e1:exp -> e2:exp -> ms:eff -> trets:typ -> wp0:typ ->         mb:eff{mb=EfPure} -> targ:typ -> tbody:typ -> wpbody:typ -> wp1:typ -> wp2:typ ->
      hvsub : validity g (sub_computation EfPure trets (tot_wp trets) EfPure (tsubst_ebeta e2 tbody) (tyapp_wp EfPure e2 targ tbody wpbody wp1 wp2)) ->
      htot : typing g (EApp e1 e2) (tot (tsubst_ebeta e2 tbody)) ->
      hvsubret : validity g (sub_computation ms trets wp0 EfPure (tsubst_ebeta e2 tbody) (return_pure (tsubst_ebeta e2 tbody) (EApp e1 e2))) ->
      app_inversion_pure g e1 e2 ms trets wp0 mb targ tbody wpbody wp1 wp2
*)

type app_inversion_res : g:env -> e1:exp -> e2:exp -> ms:eff -> trets:typ -> wp0:typ -> Type =
| AppInversion : #g:env -> #e1:exp -> #e2:exp -> #ms:eff -> #trets:typ -> #wp0:typ ->
   mb:eff{eff_sub mb ms} -> targ:typ -> tbody:typ -> wpbody:typ -> wp1:typ -> wp2:typ ->
   ht1:typing g e1 (Cmp mb (TArr targ (Cmp mb tbody wpbody)) wp1) ->
   ht2:typing g e2 (Cmp mb targ wp2) ->
   htotarg:option (typing g e2 (tot targ)){teappears 0 tbody ==> is_Some htotarg} ->
   hktbody:option (kinding g (teshd tbody) KType){not (teappears 0 tbody) ==> is_Some hktbody} ->
   hst:styping g (tsubst_ebeta e2 tbody) trets ->
   hinvtot : inversion_tot_res g (EApp e1 e2) mb (tsubst_ebeta e2 tbody) (tyapp_wp mb e2 targ tbody wpbody wp1 wp2) ms trets wp0 ->
   app_inversion_res g e1 e2 ms trets wp0


(* little change with the version of the paper : mb is the effect when the TyApp rule is applied *)



opaque val app_inversion : #g:env -> #e1:exp -> #e2:exp -> #ms:eff -> #trets:typ -> #wp0:typ ->
   ht:typing g (EApp e1 e2) (Cmp ms trets wp0) ->
   Tot (app_inversion_res g e1 e2 ms trets wp0)
(decreases %[ht])
let rec app_inversion g e1 e2 ms trets wp0 ht =
match ht with
| TyApp #x1 #x2 #x3 #x5 #targ #tbody #wpbody #wp1 #wp2 ht1 ht2 htot hk ->
(
 let hktrets : kinding g trets KType = magic() in
 let hst : styping g (tsubst_ebeta e2 tbody) trets = styping_refl #g #trets hktrets in
 let hinvtot : inversion_tot_res g (EApp e1 e2) ms (tsubst_ebeta e2 tbody) (tyapp_wp ms e2 targ tbody wpbody wp1 wp2) ms trets wp0 = magic() in
 AppInversion ms targ tbody wpbody wp1 wp2 ht1 ht2 htot hk hst hinvtot
)
| TyRet x1 htot ->
(
 let AppInversion mb targ tbody wpbody wp1 wp2 ht1 ht2 htotarg hktbody hst hvsubwp = app_inversion #g #e1 #e2 #EfPure #trets #(tot_wp trets) htot in
 let hinvtot :inversion_tot_res g (EApp e1 e2) mb (tsubst_ebeta e2 tbody) (tyapp_wp mb e2 targ tbody wpbody wp1 wp2) ms trets wp0= magic() in
 AppInversion mb targ tbody wpbody wp1 wp2 ht1 ht2 htotarg hktbody hst hinvtot
)
| TySub #x1 #x2 #c' #c ht' hsc ->
(
 let Cmp mc' tc' wpc' = c' in
 let Cmp mc tc wpc = c in
 let AppInversion mb targ tbody wpbody wp1 wp2 ht1 ht2 htotarg hktbody hst' hvsubwp = app_inversion #g #e1 #e2 #mc' #tc' #wpc' ht' in
 let hst : styping g (tsubst_ebeta e2 tbody) tc = SubTrans #g #(tsubst_ebeta e2 tbody) #tc' #tc hst' (SCmp.hs hsc) in
 let hinvtot :inversion_tot_res g (EApp e1 e2) mb (tsubst_ebeta e2 tbody) (tyapp_wp mb e2 targ tbody wpbody wp1 wp2) ms trets wp0= magic() in
 AppInversion mb targ tbody wpbody wp1 wp2 ht1 ht2 htotarg hktbody hst hinvtot
)

type if_inversion_res : g:env -> eg:exp -> et:exp -> ee:exp ->
                        ms:eff -> ts:typ -> wps:typ ->
			Type =
| IfInversion : #g:env -> #eg:exp -> #et:exp -> #ee:exp ->
                #ms:eff -> #ts:typ -> #wps:typ ->
                mb:eff{eff_sub mb ms} -> tb:typ -> wpg:typ -> wpt:typ -> wpe:typ ->
                htg:typing g eg (Cmp mb tint wpg) ->
		htt:typing g et (Cmp mb tb wpt) ->
		hte:typing g ee (Cmp mb tb wpe) ->
		hst:styping g tb ts ->
		inversion_tot_res g (EIf0 eg et ee) mb tb (ite mb tb wpg wpt wpe)
                                                   ms ts wps ->
		if_inversion_res g eg et ee ms ts wps

opaque val if_inversion : #g:env -> #eg:exp -> #et:exp -> #ee:exp ->
                   #ms:eff -> #ts:typ -> #wps:typ ->
                   ht:typing g (EIf0 eg et ee) (Cmp ms ts wps) ->
		   Tot(if_inversion_res g eg et ee ms ts wps)
(decreases %[ht])
let rec if_inversion g eg et ee ms ts wps ht =
match ht with
| TyIf0 g eg et ee m tb wpg wpt wpe htg htt hte ->
(
 let hk:kinding g tb KType = magic() in
 let hst:styping g tb tb = styping_refl hk in
 let hinvtot: inversion_tot_res g (EIf0 eg et ee) m tb (ite m tb wpg wpt wpe) ms ts wps = magic() in
 IfInversion m tb wpg wpt wpe htg htt hte hst hinvtot
)
| TyRet ts htot ->
(
 let IfInversion mb tb wpg wpt wpe htg htt hte hst hinvtot = if_inversion #g #eg #et #ee #EfPure #ts #(tot_wp ts) htot in
 let hinvtot: inversion_tot_res g (EIf0 eg et ee) mb tb (ite mb tb wpg wpt wpe) ms ts wps = magic() in
 IfInversion mb tb wpg wpt wpe htg htt hte hst hinvtot
)
| TySub #x1 #x2 #c' #c ht' hsc ->
(
 let Cmp mc tc wpc = c in
 let Cmp mc' tc' wpc' = c' in
 let IfInversion mb tb wpg wpt wpe htg htt hte hst' hinvtot = if_inversion #g #eg #et #ee #mc' #tc' #wpc' ht' in
 let hst : styping g tb tc = SubTrans #g #tb #tc' #tc hst' (SCmp.hs hsc) in
 let hinvtot: inversion_tot_res g (EIf0 eg et ee) mb tb (ite mb tb wpg wpt wpe) mc tc wpc = magic() in
 IfInversion mb tb wpg wpt wpe htg htt hte hst hinvtot
)


opaque val value_inversion : #g:env -> #e:exp{is_value e \/ is_EVar e} ->
                      #m:eff -> #t:typ -> #wp:typ ->
                      hwf:ewf g ->
                      ht:typing g e (Cmp m t wp) ->
		      Tot (cand (typing g e (tot t))
			        (validity g (ret_weakest e m t wp)))
(decreases %[ht])
let rec value_inversion g e m t wp hwf ht =
match ht with
| TyVar _         -> Conj ht (tot_ret_weakest hwf ht)
| TyConst _ _ _   -> Conj ht (tot_ret_weakest hwf ht)
| TyAbs _ _ _ _ _ -> Conj ht (tot_ret_weakest hwf ht)
| TyRet _ htot -> Conj htot (magic()) (*return_pure => return_pure … *)
| TySub #g #e #c' #c ht' hsc ->
(
 let Cmp m' t' wp' = c' in
 let Conj ht'' hv'' : cand (typing g e (tot t'))
                         (validity g (ret_weakest e m' t' wp')) = value_inversion #g #e #m' #t' #wp' hwf ht' in
 let SCmp #g m' #t' wp' m #t wp hs hk hvmono hk' hvmono' hvsub = hsc in
 let Conj hkt' hkt : cand (kinding g t' KType) (kinding g t KType) = styping_derived #g #t' #t hs in
 let hsctot : scmp g (tot t') (tot t) = sc_tot #g #t' #t hs in
 let httott : typing g e (tot t) = TySub #g #e #(tot t') #(tot t) ht'' hsctot in
 let hkreturn : kinding g (return_pure t e) (k_m EfPure t) = kdg_return_pure #g #e #t httott hkt in
 let hv : validity g (ret_weakest e m t wp) = magic() in
 Conj httott hv
)
| TyApp #g #e1 #e2 #m #targ #tbody #wpbody #wp1 #wp2 ht1 ht2 htot hk ->
(
 (* SF : this one is going to be complicated … *)
 admit()
)


opaque val subtype_with_inv_tot : #g:env -> #e:exp -> #mb:eff -> #tb:typ -> #wpb:typ ->
                           #ms:eff{eff_sub mb ms} -> #ts:typ -> #wps:typ -> #e':exp ->
			   hinvtot : inversion_tot_res g e mb tb wpb ms ts wps ->
                           ht:typing g e' (Cmp mb tb wpb) ->
			   hst:styping g tb ts ->
			   Tot(typing g e' (Cmp ms ts wps))
let subtype_with_inv_tot g e mb tb wpb ms ts wps hinvtot ht hst = admit()
*)
(*
opaque val subkinding_from_teqt : #g:env -> #k:knd -> #t1:typ -> #t2:typ -> #k':knd ->
                              hv:validity g (teqt k t1 t2) ->
			      hk:kwf (textend k g) k' ->
			      Tot (skinding g (tsubst_tbeta t1 t) (tsubst_tbeta t2 t))
let subkinding_from_teqt g k t1 t2 k' hv hk = match hk with
|
*)

opaque val pure_to_tot : #g:env -> #e:exp -> #t:typ -> #wp:typ -> #post:typ ->
   ht:typing g e (Cmp EfPure t wp) ->
   hk:kinding g post (k_pure t) -> (* <- SF : not sure if needed*)
   hv : validity g (TTApp wp post) ->
   Tot (typing g e (tot t))
let pure_to_tot g e t wp post ht hk hv = admit()

type type_from_kwf_res : env -> knd -> Type =
| TypeFromKwf : #g:env -> #k:knd ->
                t:typ ->
		kinding g t k ->
		type_from_kwf_res g k
opaque val type_from_kwf : #g:env -> #k:knd ->
     hkwf : kwf g k ->
     Tot (type_from_kwf_res g k)
(decreases %[hkwf])
let rec type_from_kwf g k hkwf =
match hkwf with
| WfType _ -> TypeFromKwf #g #k (TConst TcInt) (KConst #g #TcInt (WFTcOther g TcInt))
| WfTArr #x1 #t #k' hk hkwfbody ->
(
 let TypeFromKwf tbody hktbody = type_from_kwf #(eextend t g) #k' hkwfbody in
 TypeFromKwf #g #k (TELam t tbody) (KELam #g #t #tbody #k' hk hktbody)
)
| WfKArr #x1 #karg #kbody hkwfkarg hkwfkbody ->
(
 let TypeFromKwf tbody hktbody = type_from_kwf #(textend karg g) #kbody hkwfkbody in
 TypeFromKwf #g #k (TTLam karg tbody) (KTLam #g #karg #tbody #kbody hkwfkarg hktbody)
)


opaque val skdg_eqe : #g:env -> #e:exp -> #e':exp -> #t:typ -> #k:knd ->
   ht:typing g e (tot t) ->
   ht':typing g e' (tot t) ->
   hv:validity g (teqe t e e') ->
   hkwf : kwf (eextend t g) k ->
   Tot (skinding g (ksubst_ebeta e' k) (ksubst_ebeta e k))
let skdg_eqe g e e' t k ht ht' hv hkwf = admit()

opaque val skdg_eqt : #g:env -> #t:typ -> #t':typ -> #karg:knd -> #kbody:knd ->
   hk : kinding g t karg ->
   hk': kinding g t' karg ->
   hv:validity g (teqt karg t t') ->
   hkwf: kwf (textend karg g) kbody ->
   Tot (skinding g (ksubst_tbeta t' kbody) (ksubst_tbeta t kbody))
let skdg_eqt g t t' karg kbody hk hk' hv hkwf = admit()





opaque val pure_typing_preservation : #g:env -> #e:exp -> #e':exp -> #t:typ -> #wp:typ -> #post:typ ->
     hwf:ewf g ->
     ht:typing g e (Cmp EfPure t wp) ->
     hstep:epstep e e' ->
     hv :validity g (TTApp wp post) ->
     Tot (either (typing g e' (Cmp EfPure t wp)) (validity g tfalse))
(decreases %[ht])
opaque val pure_kinding_preservation : #g:env -> #t:typ -> #t':typ -> #k:knd ->
     hwf:ewf g ->
     hk:kinding g t k ->
     hstep:tstep t t' ->
     Tot (either (kinding g t' k) (validity g tfalse))
(decreases %[hk])

let rec pure_typing_preservation g e e' t wp post hwf ht hstep hv =
if is_TySub ht then
  let TySub #x1 #x2 #c' #c ht' hsc = ht in
  let Cmp mc' tc' wpc' = c' in
  let hv' : validity g (TTApp wpc' post) =
    (*We use the implication wp ==>_PURE wpc' contained in hsc*)
    magic() in
  match pure_typing_preservation #g #e #e' #tc' #wpc' #post hwf ht' hstep hv' with
  | Inr temp -> Inr temp
  | Inl temp ->
  (
    let ht' : typing g e' c' = temp in
    Inl (TySub #g #e' #c' #c ht' hsc)
  )
else if is_TyRet ht then
  let TyRet t htot = ht in
  let posttot = TELam t ttrue in
  let wp' = tot_wp t in
  let hv' : validity g (TTApp wp' posttot) = (*easy*) magic() in
  match pure_typing_preservation #g #e #e' #t #wp' #posttot hwf htot hstep hv' with
  | Inr temp -> Inr temp
  | Inl temp ->
  (
    let htot' : typing g e' (tot t) = temp in
    let ht' : typing g e' (Cmp EfPure t (return_pure t e')) = TyRet #g #e' t htot' in
    let hsc' : scmp g (Cmp EfPure t (return_pure t e')) (Cmp EfPure t (return_pure t e)) = (*easy with VRedE, VSubstE*) magic() in
    Inl (TySub #g #e' #(Cmp EfPure t (return_pure t e')) #(Cmp EfPure t (return_pure t e)) ht' hsc')
  )
else
match hstep with
| PsBeta targ ebody earg ->
(
 let TyApp #x1 #x2 #x3 #x4 #targs #trets #wps #wp1 #wp2 htfuns htargs htotargs hktrets = ht in
 let AbsInversion mb tretb wpb htbody hsttarrbs hvsub = abs_inversion #g #targ #ebody #EfPure #(TArr targs (Cmp EfPure trets wps)) #wp1 hwf htfuns in
 let res = styping_inv_arr' #g #targ #(Cmp mb tretb wpb) #targs #(Cmp EfPure trets wps) hwf hsttarrbs in
 match res with
 | Inr hvfalse -> Inr hvfalse (* What to do with an inconsistent environment ? *)
 | Inl temp -> (let Conj hsttarg hscmp = temp in
   let htbody : typing (eextend targs g) ebody (Cmp EfPure trets wps) =
     let htbody : typing (eextend targs g) ebody (Cmp mb tretb wpb) = esubst_with_sub_id (ebody); csubst_with_sub_id (Cmp mb tretb wpb); typing_substitution (sub_id) htbody (styping_hs (targs) (targ) hsttarg) in
     TySub #(eextend targs g) #ebody #(Cmp mb tretb wpb) #(Cmp EfPure trets wps) htbody hscmp
   in
   let htotargs : typing g earg (tot targs) =
     let post' : typ =
       (*
	fun x -> wps post
	*)
       magic()
     in
     let hkpost' : kinding g post' (k_pure targs) = magic() in
     let hvpost' : validity g (TTApp wp2 post') =
     (*
      goal : g |= wp2 (fun x -> wps post)

      We have : g |= bind wp1 (fun _ -> bind wp2 (fun x -> wps)) post
      and       g |- efun : PURE tarr wp1

      g |- efun : PURE tarr wp1
      --------------------------- V-Construct
      g |= forall post. wp1 post ==> (tarr /\ post efun)
      ------------------------------------ logical manipulation
      g |= forall post. wp1 post ==> post efun
      --------------------------------------- logical manipulation
      g |= wp1 (fun _ -> bind wp2 (fun x -> wps) post) ==> (fun _ -> bind wp2 (fun x -> wps) post) efun
      ---------------------------------------- V-ImplElim
      g |= (fun _ -> bind wp2 (fun x -> wps) post) efun
      ----------------------------------------- reduction
      g |= bind wp2 (fun x -> wps) post
      ------------------------------------ reduction
      g |= wp2 (fun x -> wps post)
      *)
       magic()
     in
     pure_to_tot #g #earg #targs #wp2 #post' htargs hkpost' hvpost'
   in
   let htred : typing g (esubst_ebeta earg ebody) (Cmp EfPure (tsubst_ebeta earg trets) (tsubst_ebeta earg wps)) = typing_substitution (sub_ebeta earg) (htbody) (ebeta_hs #g #earg #targs htotargs) in
   let wptemp = bind EfPure targs (tsubst_ebeta earg trets) wp2 (TELam targs (tyapp_wp' trets wps earg)) in
   let hvsub : validity g (sub_computation EfPure (tsubst_ebeta earg trets) (tyapp_wp EfPure earg targs trets wps wp1 wp2) EfPure (tsubst_ebeta earg trets) (tsubst_ebeta earg wps)) =
     let hv1 : validity g (sub_computation EfPure (tsubst_ebeta earg trets) wptemp EfPure (tsubst_ebeta earg trets) (tsubst_ebeta earg wps)) =
     (*
      goal : g |= bind wp2 (fun x -> wps) ==>_PURE wps[earg/x]

      g |- earg : PURE targs wp2
      -------------------------- V-Construct
      g |= forall post. wp2 post ==> (targs /\ post earg)
      ---------------------------- logical manipulation
      g |= forall post. wp2 post ==> post earg
      ----------------------------------------- logical manipulation
      g |= forall post'. wp2 (fun x -> wps post') ==> (fun x -> wps post') earg
      -------------------------------------------------------------------- beta-equivalence
      g |= forall post'. bind wp2 (fun x -> wps) post' ==> wps[earg/x] post'
      -------------------------------------------------------------- definition
      g |= bind wp2 (fun x -> wps) ==>_PURE wps[earg/x]

      *)
     magic() in
     let hv2 : validity g (sub_computation EfPure (tsubst_ebeta earg trets) (tyapp_wp EfPure earg targs trets wps wp1 wp2) EfPure (tsubst_ebeta earg trets) wptemp) =
     (*
      goal : g |= bind wp1 (fun _ -> bind wp2 (fun x -> wps)) ==>_PURE bind wp2 (fun x -> wps)

      g |- efun : PURE (targs -> PURE trets wps) wp1
      ----------------------------------------------- V-Construct
      g |= forall post. wp1 post ==> (targs -> PURE trets wps) /\ post efun
      ---------------------------------------------------------- logical manipulation
      g |= forall post. wp1 post ==> post efun
      ----------------------------------------- logical manipulation
      g |= forall post'. wp1 (fun _ -> bind wp2 (fun x -> wps) post')  ==> (fun _ -> bind wp2 (fun x -> wps) post') efun
      ------------------------------------------------ beta-equivalence
      g |= forall post'. bind wp1 (fun _ -> bind wp2 (fun x -> wps)) post' ==> bind wp2 (fun x -> wps) post'
      ----------------------------------------------------- definition
      g |= bind wp1 (fun _ -> bind wp2 (fun x -> wps)) ==>_PURE bind wp2 (fun x -> wps)
      *)
     magic()
     in
     (*transitivity of sub_computation*)
     magic()
   in
   let hscmp : scmp g (Cmp EfPure (tsubst_ebeta earg trets) (tsubst_ebeta earg wps)) (Cmp EfPure (tsubst_ebeta earg trets) (tyapp_wp EfPure earg targs trets wps wp1 wp2)) =
     let TypingDerived hktarr hkwp1 hvmono1 = typing_derived #g #(ELam targ ebody) #EfPure #(TArr targs (Cmp EfPure trets wps)) #wp1 hwf htfuns in
     let InversionTArr hktargs hktrets hkwps hvmonos = inversion_tarr #g #targs #EfPure #trets #wps hktarr in
     let hktretsearg : kinding g (tsubst_ebeta earg trets) KType = kinding_substitution (sub_ebeta earg) hktrets (ebeta_hs #g #earg #targs htotargs) in
     let hst : styping g (tsubst_ebeta earg trets) (tsubst_ebeta earg trets) = styping_refl #g #(tsubst_ebeta earg trets) hktretsearg in
     let hkwpsearg : kinding g (tsubst_ebeta earg wps) (k_pure (tsubst_ebeta earg trets)) = subst_on_k_m (sub_ebeta earg) EfPure trets; kinding_substitution (sub_ebeta earg) (hkwps) (ebeta_hs #g #earg #targs htotargs) in
     let hvmonowpsearg : validity g (monotonic EfPure (tsubst_ebeta earg trets) (tsubst_ebeta earg wps)) = subst_on_monotonic (sub_ebeta earg) EfPure trets wps; validity_substitution (sub_ebeta earg) hvmonos (ebeta_hs #g #earg #targs htotargs) in
     let TypingDerived _ hktyappwp hvmonotyapp = typing_derived hwf ht in
     SCmp #g EfPure #(tsubst_ebeta earg trets) (tsubst_ebeta earg wps) EfPure #(tsubst_ebeta earg trets) (tyapp_wp EfPure earg targs trets wps wp1 wp2) hst hktyappwp hvmonotyapp hkwpsearg hvmonowpsearg hvsub
   in
   Inl (TySub #g #(esubst_ebeta earg ebody) #(Cmp EfPure (tsubst_ebeta earg trets) (tsubst_ebeta earg wps)) #(Cmp EfPure (tsubst_ebeta earg trets) (tyapp_wp EfPure earg targs trets wps wp1 wp2)) htred hscmp)
 )
)
| PsIf0 e1 e2 ->
(
 let TyIf0 _ _ _ _ _ _ wpg wpt wpe htg htt hte = ht in
 let wpite = ite EfPure t wpg wpt wpe in
 let hsc : scmp g (Cmp EfPure t wpt) (Cmp EfPure t wpite) =
   let TypingDerived hkt hkwpt hvmonot = typing_derived #g #e1 #EfPure #t #wpt hwf htt in
   let TypingDerived _ hkwpite hvmono = typing_derived #g #(EIf0 (eint 0) e1 e2) #EfPure #t #wpite hwf ht in
   let hst : styping g t t = styping_refl #g #t hkt in
   let hvsub : validity g (sub_computation EfPure t wpite EfPure t wpt) = magic() in
   SCmp EfPure wpt EfPure wpite hst hkwpite hvmono hkwpt hvmonot hvsub in
 Inl (TySub #g #e' #(Cmp EfPure t wpt) #(Cmp EfPure t wpite) htt hsc)
)
| PsIfS i e1 e2 ->
(
 let TyIf0 _ _ _ _ _ _ wpg wpt wpe htg htt hte = ht in
 let wpite = ite EfPure t wpg wpt wpe in
 let hsc : scmp g (Cmp EfPure t wpe) (Cmp EfPure t wpite) =
   let TypingDerived hkt hkwpe hvmonoe = typing_derived #g #e2 #EfPure #t #wpe hwf hte in
   let TypingDerived _ hkwpite hvmono = typing_derived #g #(EIf0 (eint i) e1 e2) #EfPure #t #wpite hwf ht in
   let hst : styping g t t = styping_refl #g #t hkt in
   let hvsub : validity g (sub_computation EfPure t wpite EfPure t wpe) = magic() in
   SCmp EfPure wpe EfPure wpite hst hkwpite hvmono hkwpe hvmonoe hvsub in
 Inl (TySub #g #e2 #(Cmp EfPure t wpe) #(Cmp EfPure t wpite) hte hsc)
)
| PsAppE1 #efun #efun' earg hstepfun ->
(
 let TyApp #x1 #x2 #x3 #x4 #targ #tbody #wpbody #wp1 #wp2 ht1 ht2 htotarg hktbody = ht in
 let tarr = (TArr targ (Cmp EfPure tbody wpbody)) in
 let wpapp = tyapp_wp EfPure earg targ tbody wpbody wp1 wp2 in
 let postfun : typ = magic() (*(fun _ -> bind wp2 (fun x -> wp) post) *)in
 let hvpost : validity g (TTApp wp1 postfun) = magic() in
 match pure_typing_preservation #g #efun #efun' #tarr #wp1 #postfun hwf ht1 hstepfun hvpost with
 | Inr temp -> Inr temp
 | Inl temp -> let htfun' : typing g efun' (Cmp EfPure tarr wp1) = temp in
 Inl (TyApp #g #efun' #earg #EfPure #targ #tbody #wpbody #wp1 #wp2 htfun' ht2 htotarg hktbody)
)
| PsAppE2 efun #earg #earg' hsteparg ->
(
 let TyApp #x1 #x2 #x3 #x4 #targ #tbody #wpbody #wp1 #wp2 ht1 ht2 htotarg hktbody = ht in
 let tarr = (TArr targ (Cmp EfPure tbody wpbody)) in
 let wpapp = tyapp_wp EfPure earg targ tbody wpbody wp1 wp2 in
 let wpapp' = tyapp_wp EfPure earg' targ tbody wpbody wp1 wp2 in
 let postfun : typ = magic()
 (* (fun x -> wp post) *)
 in
 let hvpost : validity g (TTApp wp2 postfun) = magic()
 (*
  g |= bind wp1 ( fun _ -> bind wp2 (fun x -> wp)) post
 ------------------------------------------ VRedT*
  g |= wp1 (fun _ -> wp2 (fun x -> wp post))

and

  g |- e1 : Pure (targ -> Pure tbody wp) wp1
 ------------------------------------------- VConstr
  g |= forall p. wp1 p ==> (targ -> Pure tbody wp) /\ p e1
 ---------------------------------------------------------- VForallTypElim
  g |= wp1 (fun _ -> wp2 (fun x -> wp post)) ==> ( … ) /\ (fun _ -> wp2 (fun x -> wp post)) e1
 ---------------------------------------------------------- VImplElim
  g |= ( … ) /\ (fun _ -> wp2 (fun x -> wp post)) e1
 ----------------------------------------------------------- VAndElim2
  g |= (fun _ -> wp2 (fun x -> wp post)) e1
 -------------------------------------------------- VRedT
  g |= wp2 (fun x -> wp post) [ = wp2 postfun ]
  *)
 in
 match pure_typing_preservation #g #earg #earg' #targ #wp2 #postfun hwf ht2 hsteparg hvpost with
 | Inr temp -> Inr temp
 | Inl temp ->
 (
   let htarg' : typing g earg' (Cmp EfPure targ wp2) = temp in
   let ht' : either (typing g (EApp efun earg') (Cmp EfPure (tsubst_ebeta earg' tbody) wpapp')) (validity g tfalse) =
     if teappears 0 tbody then
       let Some htotargv = htotarg in
       let postfun : typ = magic() in
       let hvpost : validity g (TTApp (tot_wp targ) postfun) = magic() in
       (
	 match pure_typing_preservation #g #earg #earg' #targ #(tot_wp targ) #postfun hwf htotargv hsteparg hvpost with
	 | Inr temp -> Inr temp
	 | Inl temp ->
	 let htotarg' : h:option (typing g earg' (tot targ)){is_Some h} = Some temp in
	 Inl (TyApp #g #efun #earg' #EfPure #targ #tbody #wpbody #wp1 #wp2 ht1 htarg' htotarg' None)
       )
     else
       Inl (TyApp #g #efun #earg' #EfPure #targ #tbody #wpbody #wp1 #wp2 ht1 htarg' None hktbody)
   in
   match ht' with
   | Inr temp -> Inr temp
   | Inl ht'  ->
   (
     let hsc : scmp g (Cmp EfPure (tsubst_ebeta earg' tbody) wpapp') (Cmp EfPure (tsubst_ebeta earg tbody) wpapp) = magic() (* We use VRedE and VSubstE here *) in
     Inl (TySub #g #(EApp efun earg') #(Cmp EfPure (tsubst_ebeta earg' tbody) wpapp') #(Cmp EfPure (tsubst_ebeta earg tbody) wpapp) ht' hsc)
   )
 )
)
| PsLamT #targ #targ' ebody htstep ->
(
 let AbsInversion mb tretb wpb htbody hst hvwp = abs_inversion #g #targ #ebody #EfPure #t #wp hwf ht in
 let TyAbs mb tretb wpb hktarg htbody = ht in
 match pure_kinding_preservation #g #targ #targ' #KType hwf hktarg htstep with
 | Inr temp -> Inr temp
 | Inl temp ->
 (
   let hktarg' : kinding g targ' KType = temp in
   let hvarg : validity g (teqtype targ targ') = VRedT #g #targ #targ' #KType hktarg hktarg' htstep in
   let hstarg : styping g targ' targ =
     let hvarg' : validity g (teqtype targ' targ) = v_eq_symt #g #targ #targ' #KType hvarg in
     SubConv #g #targ targ' hvarg' hktarg hktarg' in
   let htbody' : typing (eextend targ' g) ebody (Cmp mb tretb wpb) = esubst_with_sub_id ebody; csubst_with_sub_id (Cmp mb tretb wpb); typing_substitution (sub_id) (htbody) (styping_hs #g targ' targ hstarg) in
   let tarr' = TArr targ' (Cmp mb tretb wpb) in
   let tarr = TArr targ (Cmp mb tretb wpb) in
   let htfun : typing g (ELam targ' ebody) (tot tarr') = TyAbs #g #targ' #ebody mb tretb wpb hktarg' htbody' in
   let hsttarr : styping g tarr' tarr =
     let hstarg : styping g targ targ' =
       SubConv #g #targ' targ hvarg hktarg' hktarg in
     let TypingDerived hktretb hkwpb hvmono = typing_derived (GType hwf hktarg) htbody in
     let hscbody : scmp (eextend targ g) (Cmp mb tretb wpb) (Cmp mb tretb wpb) = scmp_refl #(eextend targ g) #mb #tretb #wpb hktretb hkwpb hvmono in
     let hktarr' : kinding g tarr' KType =
       let TypingDerived hktarr' _ _ = typing_derived #g #(ELam targ' ebody) #EfPure #tarr' #(tot_wp tarr') hwf htfun in hktarr' in
     SubFun #g #targ #targ' #(Cmp mb tretb wpb) #(Cmp mb tretb wpb) hstarg hscbody hktarr' in
   let hsttot : scmp g (tot tarr') (tot tarr) = magic() in
   Inl (TySub #g #(ELam targ' ebody) #(tot tarr') #(tot tarr) htfun hsttot)
 )
)
| PsIf0E0 #e0 #e0' ethen eelse hstep ->
(
  let TyIf0 _ _ _ _ _ _ wpg wpt wpe htg htt hte = ht in
  let postwpg = magic()
  (*
   fun x ->
     x = 0  ==> wpt post
  /\ x <> 0 ==> wpe post
   *)
  in
  let hv' : validity g (TTApp wpg postwpg) = magic()
  (*
   g |= bind wpg (fun x -> ((x = 0)^ ==>_PURE wpt /\_PURE (x <> 0)^ ==>_PURE wpe)) post
  ------------------------------------------------ VRedT*
   g |= wpg (fun x -> (x=0 ==> wpt post) /\ (x<>0 ==> wpe post)) [= wpg postwpg]
   *)
  in
  match pure_typing_preservation #g #e0 #e0' #tint #wpg #postwpg hwf htg hstep hv' with
  | Inr temp -> Inr temp
  | Inl temp ->
  (
    let htg' : typing g e0' (Cmp EfPure tint wpg) = temp in
    Inl (TyIf0 g e0' ethen eelse EfPure t wpg wpt wpe htg' htt hte)
  )
)
| PsFixPure tx t' t'' wpfix d f v ->
(

 let TyApp #x1 #x2 #x3 #x4 #targ3s #tfun3s #wpbody3s #wpfun3s #wparg3s htfun3 htarg3 htot3 hk3 = ht in
(* Sketch of the proof :
  * I call base types the ones that are built with tx t' t'' wpfix without subtyping
  * we get a tot proof for 'd', 'f', 'v' with base types with the same technic than in TyApp using the subtyping relations we get when we invert the typing judgement
  * we convert them to return proofs
  * we get a typing proof for 'fix_pure d f' and we subsume it in order for the type to match the one of the second argument of f (everything with base types), still with a 'return' wp for 'fix_pure d f'
  * we get a typing proof for 'f v (fix_pure d f)' that is of type "t'' v" and wp "wpfix v"
  * we show that g |- t'' v <: t and g |= wpbody3s[v/x] ==>_PURE wpfix v with the different subcomputation relations we have
  * we show with V-Constr, that g |= bind wpfun3s (fun _ -> bind wparg3s (fun x -> wpbody3s)) ==>_PURE bind wparg3s (fun x -> wpbody3s)
  and g |= bind wparg3s (fun x -> wpbody3s) ==> wpbody3s[v/x]
  * so we can subsume a last time and get what we want
 *)
 let tdb = tfixpured tx t' in
 let tfb = tsubst_ebeta d (tfixpureF tx t'' wp) in
 let tvb = tx in
 (* We first get the fact that the argument have the right base type
  and the return wp *)
 let htd : typing g d (return_pure_cmp tdb d) = magic() in
 let htf : typing g f (return_pure_cmp tfb f) = magic() in
 let htv : typing g v (return_pure_cmp tvb v) = magic() in
 (* We first build the proof that fix_pure d F has the good type to be
  the second argument of F *)
 (*
 let htfix : typing g (eapp2 (EConst (EcFixPure tx t' t'' wpfix)) d f)
             (return_pure_cmp (TArr tx (Cmp EfPure (TEApp (tesh t'') (EVar 0)) (op_pure (TEApp (tesh t'') (EVar 0)) tand (up_pure (TEApp (tesh t'') (EVar 0)) (tprecedes (EApp d (EVar 0)) (EApp d v))) (TEApp (tesh wpfix) (EVar 0))))) (eapp2 (EConst (EcFixPure tx t' t'' wpfix)) d f)) = magic() in
 *)
 (* We now get the fact that the final expression has the good base type (the fact that we have the 'return' wp for all arguments let us reduce to the final wp directly*)
 let htappb : typing g (eapp2 f v (eapp2 (EConst (EcFixPure tx t' t'' wpfix)) d f)) (Cmp EfPure (TEApp t'' v) (TEApp wpfix v)) = magic() in
 (* We can use the different subtyping relation we have to get that the base computation and the subsumed one are related *)
 let hscmp : scmp g (Cmp EfPure (TEApp t'' v) (TEApp wpfix v)) (Cmp EfPure t wp) = magic() in
 magic()(*
 Inl (TySub #g #(eapp2 f v (eapp2 (EConst (EcFixPure tx t' t'' wpfix)) d f)) #(Cmp EfPure (TEApp t'' v) (TEApp wpfix v)) #(Cmp EfPure t wp) htappb hscmp)
 *)
 (* SF : I will not be able to prove this with F*.
  It already can not go through the sketch only *)
)
| PsSel h l ~>
(
 let TyApp #x1 #x2 #x3 #x4 #targ2s #tret2s #wpbody2s #wpfun2s #wparg2s htfun2 htarg2 htotarg2 hkarg2 = ht in
 let tfun2s = TArr targ2s (Cmp EfPure tret2s wpbody2s) in
 let RemoveSub capp1s hscapp1 htapp1 = remove_subtyping #g #(EApp (EConst EcSel) (eheap h)) #(Cmp EfPure tfun2s wpfun2s) hwf htfun2 in
 let TyApp #x1 #x2 #x3 #x4 #targ1s #tret1s #wpbody1s #wpfun1s #wparg1s htfun1 htarg1 htotarg1 hkarg1 = htapp1 in
 let htotarg1 : typing g (eheap h) (tot targ1s) = magic() in
 let tfun1s = TArr targ1s (Cmp x4 tret1s wpbody1s) in
 let RemoveSub cfun1b hscfun1 htfun1b = remove_subtyping #g #(EConst EcSel) #(Cmp x4 tfun1s wpfun1s) hwf htfun1 in
 (*
 let TyConst _ _ _ = htfun1b in
 let tfun1b = TArr theap (tot (TArr tref (tot tint))) in
 match styping_inversion_arrow #g #theap #(tot (TArr tref (tot tint))) hwf (get_styping_from_scmpex #g #(EConst EcSel) #cfun1b #(Cmp EfPure tfun1s wpfun1s) hscfun1) with
 | Inr temp -> magic()
 | Inl temp ->
 let StypingInvArr _ cfun1s hstarg1 hscbody1 = temp in
 let hstbody1 : styping g (TArr tref (tot tint)) (tsubst_ebeta (eheap h) tret1s) = subst_on_tot (sub_elam (sub_ebeta (eheap h))) tint; styping_substitution (sub_ebeta (eheap h)) (SCmp.hs hscbody1) (ebeta_hs #g #(eheap h) #targ1s htotarg1) in
 *)
 magic()
)
| _ -> admit()
and pure_kinding_preservation g t t' k hwf hk hstep =
if is_KSub hk then
let KSub #g #t #k' #k hk' hsk = hk in
 match pure_kinding_preservation hwf hk' hstep with
 | Inr temp -> Inr temp
 | Inl temp ->
 (
   let hkt': kinding g t' k' = temp in
   Inl (KSub #g #t' #k' #k hkt' hsk)
 )
else
(
 match hstep with
 | TsEBeta tx t e ->
 (
  let KEApp #x1 #x2 #targs #kbodys  hkfun htarg hw = hk in
  let InversionTELam kbodyb hktarg hktbody hsk = inversion_telam #g #tx #t #(KTArr targs kbodys) hkfun in
  let hktbody' : kinding (eextend targs g) t kbodys =
    if KTArr targs kbodys = KTArr tx kbodyb then
      hktbody
    else
      let Some hsk = hsk in
      let KSubTArr hstarg hskbody hkw1 = hsk in
      let hktbody : kinding (eextend targs g) t kbodyb = tsubst_with_sub_id t; ksubst_with_sub_id kbodyb; kinding_substitution (sub_id) hktbody (styping_hs targs tx hstarg) in
      KSub #(eextend targs g) #t #kbodyb #kbodys hktbody hskbody
  in
  Inl (kinding_substitution (sub_ebeta e) (hktbody') (ebeta_hs #g #e #targs htarg))
 )
 | TsTBeta karg tbody targ ->
 (
  let KTApp #x1 #x2 #x3 #kargs kbodys hkfun hkarg hw = hk in
  let InversionTTLam kbodyb hkwfkarg hktbody hsk = inversion_ttlam #g #karg #tbody #(KKArr kargs kbodys) hkfun in
  let hktbody' : kinding (textend kargs g) tbody kbodys =
    if KKArr kargs kbodys = KKArr karg kbodyb then
      hktbody
    else
      let Some hsk = hsk in
      let KSubKArr _ _ hskarg hskbody hkw1 = hsk in
      let hktbody : kinding (textend kargs g) tbody kbodyb = tsubst_with_sub_id tbody; ksubst_with_sub_id kbodyb; kinding_substitution (sub_id) hktbody (skinding_hs kargs karg hskarg) in
      KSub #(textend kargs g) #tbody #kbodyb #kbodys hktbody hskbody
  in
  Inl (kinding_substitution (sub_tbeta targ) hktbody' (tbeta_hs #g #targ #kargs hkarg))
 )
 | TsArrT1 #t1 #t1' c hsteparg ->
 (
  let Cmp mc tc wpc = c in
  let KArr hkt1 hktc hkwp hvmono = hk in
  match pure_kinding_preservation #g #t1 #t1' #KType hwf hkt1 hsteparg with
  | Inr temp -> Inr temp
  | Inl temp ->
  (
    let hkt1' : kinding g t1' KType = temp in
    let hs : subst_typing (sub_id) (eextend t1 g) (eextend t1' g) =
      let heq : validity g (teqtype t1 t1') = VRedT #g #t1 #t1' #KType hkt1 hkt1' hsteparg in
      let heq : validity g (teqtype t1' t1) = v_eq_symt #g #t1 #t1' #KType heq in
      let hst:styping g t1' t1 = SubConv #g #t1 t1' heq hkt1 hkt1' in
      styping_hs #g t1' t1 hst
    in
    let hktc':kinding (eextend t1' g) tc KType = tsubst_with_sub_id tc; kinding_substitution (sub_id) (hktc) (hs) in
    let hkwp':kinding (eextend t1' g) wpc (k_m mc tc) = tsubst_with_sub_id wpc; ksubst_with_sub_id (k_m mc tc); kinding_substitution (sub_id) (hkwp) (hs) in
    let hvmono' : validity (eextend t1' g) (monotonic mc tc wpc) = tsubst_with_sub_id (monotonic mc tc wpc); validity_substitution (sub_id) (hvmono) (hs) in
    let hktarr' : kinding g (TArr t1' (Cmp mc tc wpc)) KType = KArr #g #t1' #tc #wpc #mc hkt1' hktc' hkwp' hvmono' in
    Inl hktarr'
  )
 )
 | TsTAppT1 #t1 #t1'  t2 hstepfun ->
 (
  let KTApp #x1 #x2 #x3 #k k' hkt1 hkt2 hkw = hk in
  match pure_kinding_preservation #g #t1 #t1' #(KKArr k k') hwf hkt1 hstepfun with
  | Inr temp -> Inr temp
  | Inl temp ->
  (
    let hkt1' : kinding g t1' (KKArr k k') = temp in
    Inl (KTApp #g #t1' #t2 #k k' hkt1' hkt2 hkw)
  )
 )
 | TsTAppT2 t1 #t2 #t2' hsteparg ~>
 (
  let KTApp #x1 #x2 #x3 #k k' hkt1 hkt2 hkw = hk in
  match pure_kinding_preservation #g #t2 #t2' #k hwf hkt2 hsteparg with
  | Inr temp -> Inr temp
  | Inl temp ->
  (
    let hkt2': kinding g t2' k = temp in
    let hkwfkarr : kwf g (KKArr k k') = kinding_derived hwf hkt1 in
    let WfKArr hkwfk hkwfk' = hkwfkarr in
    let hkw : kwf g (ksubst_tbeta t2' k') = kwf_substitution #(textend k g) (sub_tbeta t2') #g (hkwfk') (tbeta_hs #g #t2' #k hkt2') in
    let hv : validity g (teqt k t2 t2') = VRedT #g #t2 #t2' #k hkt2 hkt2' hsteparg in
    let hsk : skinding g (ksubst_tbeta t2' k') (ksubst_tbeta t2 k') = skdg_eqt #g #t2 #t2' #k #k' hkt2 hkt2' hv hkwfk' in
    let hk : kinding g (TTApp t1 t2') (ksubst_tbeta t2' k') = KTApp #g #t1 #t2' #k k' hkt1 hkt2' hkw in
    Inl (KSub #g #(TTApp t1 t2') #(ksubst_tbeta t2' k') #(ksubst_tbeta t2 k') hk hsk)
    (* SF : we need : t = t' => k[t/x] <:> k[t'/x]*)
  )
 )
 | TsEAppT #t #t' e hstepfun ->
 (
  let KEApp #x1 #t #targ #kbody #e hkt hte hkwf = hk in
  match pure_kinding_preservation #g #t #t' #(KTArr targ kbody) hwf hkt hstepfun with
  | Inr temp -> Inr temp
  | Inl temp ->
  (
    let hkt' : kinding g t' (KTArr targ kbody) = temp in
    Inl (KEApp #g #t' #targ #kbody #e hkt' hte hkwf)
  )
 )
 | TsEAppE t #e #e' hsteparg ~>
 (
  let KEApp #x1 #x2 #targ #kbody #x3 hkt hte hkwf = hk in
  let post : typ = magic() in
  let hv : validity g (TTApp (tot_wp targ) post) = magic() in
  match pure_typing_preservation #g #e #e' #targ #(tot_wp targ) #post hwf hte hsteparg hv with
  | Inr temp -> Inr temp
  | Inl temp ->
  (
   let hte' : typing g e' (tot targ) = temp in
   let hkwfkarr : kwf g (KTArr targ kbody) = kinding_derived hwf hkt in
   let WfTArr _ hkwfkbody = hkwfkarr in
   let hkw : kwf g (ksubst_ebeta e' kbody) = kwf_substitution (sub_ebeta e') hkwfkbody (ebeta_hs #g #e' #targ hte') in
   let hv : validity g (teqe targ e e') = VRedE #g #e #targ #e' hte hte' hsteparg in
   let hsk : skinding g (ksubst_ebeta e' kbody) (ksubst_ebeta e kbody) = skdg_eqe #g #e #e' #targ #kbody hte hte' hv hkwfkbody in
   let hk : kinding g (TEApp t e') (ksubst_ebeta e' kbody) = KEApp #g #t #targ #kbody #e' hkt hte' hkw in
   Inl (KSub #g #(TEApp t e') #(ksubst_ebeta e' kbody) #(ksubst_ebeta e kbody) hk hsk)
  )
  (* SF : we need : e = e' => k[e/x] <:> k[e'/x]*)
 )
 | TsTLamT k #t #t' hstep ->
 (
  let KTLam #x1 #x2 #x3 #k' hkwfk hkt = hk in
  let hwfext : ewf (textend k g) = GKind hwf hkwfk in
  match pure_kinding_preservation #(textend k g) #t #t' #k' hwfext hkt hstep with
  | Inr temp ->
  (
   let TypeFromKwf targ hktarg = type_from_kwf #g #k hkwfk in
   Inr (validity_substitution (sub_tbeta targ) temp (tbeta_hs #g #targ #k hktarg))
  )
  | Inl temp ->
  (
    let hkt' : kinding (textend k g) t' k' = temp in
    Inl (KTLam #g #k #t' #k' hkwfk hkt' )
  )
 )
 | TsELamT1 #t1 #t1' t2 hsteparg ->
 (
  let KELam #x1 #x2 #x3 #kbody hkt1 hkt2 = hk in
  match pure_kinding_preservation #g #t1 #t1' #KType hwf hkt1 hsteparg with
  | Inr temp -> Inr temp
  | Inl temp ->
  (
    let hkt1' : kinding g t1' KType = temp in
    let hveq:validity g (teqtype t1 t1') = VRedT #g #t1 #t1' #KType hkt1 hkt1' hsteparg in
    let hveq':validity g (teqtype t1' t1) = v_eq_symt #g #t1 #t1' #KType hveq in
    let hst' : styping g t1' t1 = SubConv #g #t1 t1' hveq' hkt1 hkt1' in
    let hktemp : kinding g (TELam t1' t2) (KTArr t1' kbody) = tsubst_with_sub_id t2; ksubst_with_sub_id kbody; KELam #g #t1' #t2 #kbody hkt1' (kinding_substitution (sub_id) hkt2 (styping_hs t1' t1 hst')) in
    let hsk: skinding g (KTArr t1' kbody) (KTArr t1 kbody) =
      let hst : styping g t1 t1' = SubConv #g #t1' t1 hveq hkt1' hkt1 in
      let hwfext : ewf (eextend t1 g) = GType hwf hkt1 in
      let hkwf2 : kwf (eextend t1 g) kbody = kinding_derived #(eextend t1 g) #t2 #kbody hwfext hkt2 in
      let hskbody : skinding (eextend t1 g) kbody kbody = KSubRefl #(eextend t1 g) #kbody hkwf2 in
      let hkwfarr : kwf g (KTArr t1' kbody) = kinding_derived #g #(TELam t1' t2) #(KTArr t1' kbody) hwf hktemp in
      KSubTArr #g #t1' #t1 #kbody #kbody hst hskbody hkwfarr
    in
    Inl (KSub #g #(TELam t1' t2) #(KTArr t1' kbody) #(KTArr t1 kbody) hktemp hsk)
  )
 )
)

type pure_progress_res : exp -> Type =
| PureProgress : #e:exp ->
    e' :exp ->
    epstep e e' ->
    pure_progress_res e


assume val empty_consistent : validity empty tfalse -> Lemma (false)

opaque val styping_inversion_arrow_empty : #t1:typ -> #c1:cmp -> #t:typ ->
  hst:styping empty (TArr t1 c1) t ->
  Tot (styping_inv_arr_res empty t1 c1 t)
let styping_inversion_arrow_empty t1 c1 t hst = magic()

opaque val value_inversion_empty : #e:exp{is_value e \/ is_EVar e} ->
                      #m:eff -> #t:typ -> #wp:typ ->
                      ht:typing empty e (Cmp m t wp) ->
		      Tot (typing empty e (tot t))
let value_inversion_empty e m t wp = admit()

type theap_inversion_res : exp -> Type =
| TheapInversion : e:exp ->
     h:heap ->
     heq : ceq e (EConst (EcHeap h)) ->
     theap_inversion_res e
opaque val theap_inversion : #g:env -> #v:value -> #wp:typ ->
   ht:typing g v (Cmp EfPure theap wp) ->
   Tot (either (theap_inversion_res v) (validity g tfalse))
let theap_inversion g v wp ht = admit()


type tref_inversion_res : exp -> Type =
| TrefInversion : e:exp ->
    l:loc ->
    heq : ceq e (EConst (EcLoc l)) ->
    tref_inversion_res e
opaque val tref_inversion : #g:env -> #v:value -> #wp:typ ->
   ht:typing g v (Cmp EfPure tref wp) ->
   Tot (either (tref_inversion_res v) (validity g tfalse))
let tref_inversion g v wp ht = admit()


type tint_inversion_res : exp -> Type =
| TintInversion : e:exp ->
    i:int ->
    heq : ceq e (EConst (EcInt i)) ->
    tint_inversion_res e
opaque val tint_inversion : #g:env -> #v:value -> #wp:typ ->
   ht:typing g v (Cmp EfPure tint wp) ->
   Tot (either (tint_inversion_res v) (validity g tfalse))
let tint_inversion g v wp ht = admit()

opaque val tint_inversion_styping' : #t':typ -> #t:typ ->
   hst : styping empty t' t ->
   hv : validity empty (teqtype t tint) ->
   Tot (validity empty (teqtype t' tint))
(decreases %[hst])
let rec tint_inversion_styping' t' t hst hv =
match hst with
| SubConv t' hv2 _ _ -> v_eq_trant #empty #t' #t #tint #KType hv2 hv
| SubTrans #x1 #t1 #t2 #t3 hs12 hs23 ->
(
 let hv2 : validity empty (teqtype t2 tint) = tint_inversion_styping' #t2 #t3 hs23 hv in
 tint_inversion_styping' #t1 #t2 hs12 hv2
)
| SubFun #g #t #t' #c' #c hstarg hsc hk' ->
(
 let Conj hktarr' hktarr = styping_derived #empty #(TArr t' c') #(TArr t c) hst in
 let hvnot : validity empty (tnot (teqtype (TArr t c) tint)) = VDistinctTH #empty #(TArr t c) #tint hktarr (kdg_tint empty) in
 let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype (TArr t c) tint) #tfalse hvnot hv in
 let hv : validity empty (teqtype (TArr t' c') tint) = empty_consistent hvfalse; hv in
 hv
)

opaque val tint_inversion_styping : #t':typ ->
  hst : styping empty t' tint ->
  Tot (validity empty (teqtype t' tint))
let tint_inversion_styping t' hst =
  let hv : validity empty (teqtype tint tint) =
    VEqReflT #empty #tint #KType (kdg_tint empty) in
  tint_inversion_styping' #t' #tint hst hv


opaque val tint_inversion_empty_helper :
   e:exp -> targ : typ -> cbody : cmp -> t:typ ->
   hst : styping empty (TArr targ cbody) t ->
   hv : validity empty (teqtype t tint) ->
   Tot (tint_inversion_res e)
let tint_inversion_empty_helper e targ cbody t hst hv =
  let Conj hktarr hk = styping_derived #empty #(TArr targ cbody) #t hst in
  let hv : validity empty (teqtype (TArr targ cbody) tint) = tint_inversion_styping' #(TArr targ cbody) #t hst hv in
  let hvnot : validity empty (tnot (teqtype (TArr targ cbody) tint)) = VDistinctTH #empty #(TArr targ cbody) #tint hktarr (kdg_tint empty) in
   let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype (TArr targ cbody) tint) #tfalse hvnot hv in
   empty_consistent hvfalse; TintInversion e 42 Refl

val scmpex_efpure : #g:env -> #e:exp -> #c':cmp -> #c:cmp ->
   scmpex g e c' c ->
   Lemma (requires (Cmp.m c = EfPure)) (ensures (Cmp.m c' = EfPure))
let scmpex_efpure g e c' c hsc = admit()





(*
//{{{
opaque val tint_inversion_empty' : #v:value -> #t:typ -> #wp:typ ->
   ht:typing empty v (Cmp EfPure t wp) ->
   hv:validity empty (teqtype t tint) ->
   Tot (tint_inversion_res v)
(decreases %[ht])
let rec tint_inversion_empty' v t wp ht hv =
match ht with
| TySub #x1 #x2 #c' #c ht' hsc ->
(
 let Cmp mc tc wpc = c in
 let Cmp mc' tc' wpc' = c' in
 let hst : styping empty tc' tc = SCmp.hs hsc in
 let hv : validity empty (teqtype tc' tint) = tint_inversion_styping' #tc' #tc hst hv in
 tint_inversion_empty' #v #tc' #wpc' ht' hv
)
| TyRet #x1 #x2 t htot ->
(
 tint_inversion_empty' #v #t #(tot_wp t) htot hv
)
| TyConst _ c hwf ->
(
 match c with
 | EcInt i -> TintInversion v i (Eq exp (EConst (EcInt i)))
 | EcUnit
 | EcLoc _
 | EcHeap _
 | EcBang
 | EcAssign
 | EcSel
 | EcUpd
 | EcFixPure _ _ _ _
 | EcFixOmega _ _ _ ->(
     let hk : kinding empty (econsts c) KType = kdg_econst empty c hwf in
     let hvnot : validity empty (tnot (teqtype t tint)) = VDistinctTH #empty #t #tint hk (kdg_tint empty) in
     let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype t tint) #tfalse hvnot hv in
     empty_consistent hvfalse; TintInversion v 42 (Eq exp (EConst (EcInt 42)))
   )
)
| TyAbs #x1 #targ #ebody m tbody wpbody hktarg htbody ->
(
 let hk : kinding empty (TArr targ (Cmp m tbody wpbody)) KType = let TypingDerived hk _ _ = typing_derived #empty #(ELam targ ebody) #EfPure #(TArr targ (Cmp m tbody wpbody) ) (GEmpty) ht in hk in
 let hvnot : validity empty (tnot (teqtype t tint)) = VDistinctTH #empty #t #tint hk (kdg_tint empty) in
 let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype t tint) #tfalse hvnot hv in
 empty_consistent hvfalse; TintInversion v 42 (Eq exp (EConst (EcInt 42)))
)
| TyApp #x1 #e1 #e2 #x2 #targs1 #tbodys1 #wps1 #wpfuns1 #wpargs1 htfuns1 htargs1 htotargs1 hkargs1 ->
(
 let tarr1 = TArr targs1 (Cmp EfPure tbodys1 wps1) in
 (
  let RemoveSub c1 hsc1 ht' = remove_subtyping #empty #e1 #(Cmp EfPure tarr1 wpfuns1) (GEmpty) htfuns1 in
  let hst1 : styping empty (Cmp.t c1) tarr1 = get_styping_from_scmpex #empty #e1 #c1 #(Cmp EfPure tarr1 wpfuns1) hsc1 in
  match e1 with
  | EConst ec ->
    (
     let TyConst _ _ _ = ht' in
     match ec with
     | EcFixOmega _ _ _
     | EcFixPure _ _ _ _ ->
     (
      (* Partially applied EcFixPure with 1 argument, so its type is a supertype of an arrow. It is too hard to manipulate the type of fixpure so I skip this part. For a more complete proof, see EcUpd. The proof is basically the same *)
      let targ : typ = magic() in
      let cbody : cmp = magic() in
      let hst : styping empty (TArr targ cbody) t = magic() in
      tint_inversion_empty_helper v targ cbody t hst hv
     )
     | EcUpd ->
     (
      magic()(*
      let StypingInvArr x1 x2 hstarg1 hscbody1 = styping_inversion_arrow_empty #theap #(tot (TArr tref (tot (TArr tint (tot theap))))) #tarr1 hst1 in
      let hst : styping (eextend targs1 empty) (TArr tref (tot (TArr tint (tot theap)))) tbodys1 = SCmp.hs hscbody1 in
      let htotarg : typing empty e2 (tot targs1) = value_inversion_empty #e2 #EfPure #targs1 #wpargs1 htargs1 in
      let hst : styping empty (TArr tref (csubst (sub_elam (sub_ebeta e2)) (tot (TArr tint (tot theap))))) (tsubst_ebeta e2 tbodys1) = styping_substitution (sub_ebeta e2) hst (ebeta_hs #empty #e2 #targs1 htotarg) in
      let targ = tref in
      let cbody = (csubst (sub_elam (sub_ebeta e2)) (tot (TArr tint (tot theap)))) in
      tint_inversion_empty_helper v targ cbody t hst hv
      *)
     )
     | EcSel ->
     (
      magic()(*
      let StypingInvArr x1 x2 hstarg1 hscbody1 = styping_inversion_arrow_empty #theap #(tot (TArr tref (tot tint))) #tarr1 hst1 in
      let hst : styping (eextend targs1 empty) (TArr tref (tot tint)) tbodys1 = SCmp.hs hscbody1 in
      let htotarg : typing empty e2 (tot targs1) = value_inversion_empty #e2 #EfPure #targs1 #wpargs1 htargs1 in
      let hst : styping empty (TArr tref (tot (tint))) (tsubst_ebeta e2 tbodys1) = subst_on_tot (sub_elam (sub_ebeta e2)) tint; styping_substitution (sub_ebeta e2) hst (ebeta_hs #empty #e2 #targs1 htotarg) in
      let targ = tref in
      let cbody = tot tint in
      tint_inversion_empty_helper v targ cbody t hst hv
      *)
     )
     | EcAssign ->
     (
      magic()(*
      let cmpb = cmp_assign (EVar 1) (EVar 0) in
      let StypingInvArr x1 x2 hstarg1 hscbody1 = styping_inversion_arrow_empty #tref #(tot (TArr tint (cmpb))) #tarr1 hst1 in
      let hst : styping (eextend targs1 empty) (TArr tint cmpb) tbodys1 = SCmp.hs hscbody1 in
      let htotarg : typing empty e2 (tot targs1) = value_inversion_empty #e2 #EfPure #targs1 #wpargs1 htargs1 in
      let hst : styping empty (TArr tint (csubst (sub_elam (sub_ebeta e2)) cmpb)) (tsubst_ebeta e2 tbodys1) = styping_substitution (sub_ebeta e2) hst (ebeta_hs #empty #e2 #targs1 htotarg) in
      let targ = tint in
      let cbody = (csubst (sub_elam (sub_ebeta e2)) cmpb) in
      tint_inversion_empty_helper v targ cbody t hst hv
      *)
     )
    )
  | EApp e11 e12 ->
  (
   scmpex_efpure #empty #e1 #c1 #(Cmp EfPure tarr1 wpfuns1) hsc1;
   let TyApp #x1 #x2 #x3 #x4 #targs2 #tbodys2 #wps2 #wpfuns2 #wpargs2 htfuns2 htargs2 htotargs2 hktargs2 = ht' in
   let tarr2 = TArr targs2 (Cmp EfPure tbodys2 wps2) in
   let RemoveSub c2 hsc2 ht' = remove_subtyping #empty #e11 #(Cmp EfPure tarr2 wpfuns2) (GEmpty) htfuns2 in
   match e11 with
   | EConst ec11 ->
   (
    match ec11 with
    | EcFixPure tx t' t'' wp ->
    (
      (* It is still the same argument, but it is still too hard to manipulate *)
      let targ : typ = magic() in
      let cbody : cmp = magic() in
      let hst : styping empty (TArr targ cbody) t = magic() in
      tint_inversion_empty_helper v targ cbody t hst hv
    )
    | EcUpd ~>
    (
     let TyConst _ _ _ = ht' in
     let hst2 = get_styping_from_scmpex #empty #e11 #c2 #(Cmp EfPure tarr2 wpfuns2) hsc2 in
     let StypingInvArr x1 x2 hstarg2 hscbody2 = styping_inversion_arrow_empty #theap #(tot (TArr tref (tot (TArr tint (tot theap))))) #tarr2 hst2 in
     let tarrb = (TArr tref (tot (TArr tint (tot theap)))) in
     let hst : styping (eextend targs2 empty) tarrb tbodys2 = SCmp.hs hscbody2 in
     let htotarg2 : typing empty e12 (tot targs2) = magic() in
     let lemma : unit -> Lemma (tsubst_ebeta e12 tarrb = tarrb) = magic() in
     (*
     fun x ->
     (
       subst_on_tot (sub_elam (sub_ebeta e12)) (TArr tint (tot theap));
       subst_on_tot (sub_elam (sub_elam (sub_ebeta e12))) theap
       (* SF : this proof should be able to work … *)
     )
     *)
     let hsttemp : styping empty (tarrb) (Cmp.t c1) =
       lemma ();
       styping_substitution (sub_ebeta e12) hst (ebeta_hs #empty #e12 #targs2 htotarg2)
     in
     let hst1 : styping empty tarrb tarr1 =
       SubTrans #empty #(TArr tref (tot (TArr tint (tot (theap))))) #(Cmp.t c1) #tarr1 hsttemp hst1
     in
     let StypingInvArr x1 x2 hstarg1 hscbody1 = styping_inversion_arrow_empty #tref #(tot (TArr tint (tot (theap)))) #tarr1 hst1 in
     let hst : styping (eextend targs1 empty) (TArr tint (tot (theap))) tbodys1 = SCmp.hs hscbody1 in
     let hst : styping empty (TArr tint (tot theap)) (tsubst_ebeta e2 tbodys1) =
       let htotarg1 : typing empty e2 (tot targs1) = magic() in
       subst_on_tot (sub_elam (sub_ebeta e2)) theap;
       styping_substitution (sub_ebeta e2) hst (ebeta_hs #empty #e2 #targs1 htotarg1)
     in
     let targ = tint in
     let cbody = tot theap in
     tint_inversion_empty_helper v targ cbody t hst hv
    )
   )
  )
 )
)
//}}}
*)
opaque val tb_inversion_styping' : #t':typ -> #t:typ -> #tc:tconst{is_TcHeap tc \/ is_TcInt tc \/ is_TcRefInt tc} ->
   hst : styping empty t' t ->
   hv : validity empty (teqtype t (TConst tc)) ->
   Tot (validity empty (teqtype t' (TConst tc)))
(decreases %[hst])
let rec tb_inversion_styping' t' t tc hst hv =
match hst with
| SubConv t' hv2 _ _ -> v_eq_trant #empty #t' #t #(TConst tc) #KType hv2 hv
| SubTrans #x1 #t1 #t2 #t3 hs12 hs23 ->
(
 let hv2 : validity empty (teqtype t2 (TConst tc)) = tb_inversion_styping' #t2 #t3 #tc hs23 hv in
 tb_inversion_styping' #t1 #t2 #tc hs12 hv2
)
| SubFun #g #t #t' #c' #c hstarg hsc hk' ->
(
 let Conj hktarr' hktarr = styping_derived #empty #(TArr t' c') #(TArr t c) hst in
 let hvnot : validity empty (tnot (teqtype (TArr t c) (TConst tc))) = VDistinctTH #empty #(TArr t c) #(TConst tc) hktarr (kdg_tb empty tc) in
 let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype (TArr t c) (TConst tc)) #tfalse hvnot hv in
 let hv : validity empty (teqtype (TArr t' c') (TConst tc)) = empty_consistent hvfalse; hv in
 hv
)
type tb_inversion_res : exp -> tconst -> Type =
| TcHeapInversion : e : exp ->
                    theap_inversion_res e ->
		    tb_inversion_res e TcHeap
| TcIntInversion : e:exp ->
                   tint_inversion_res e ->
		   tb_inversion_res e TcInt
| TcRefInversion : e:exp ->
                    tref_inversion_res e ->
		    tb_inversion_res e TcRefInt

opaque val tb_inversion_empty_helper :
   e:exp -> targ : typ -> cbody : cmp -> t:typ -> tc:tconst{is_TcHeap tc \/ is_TcInt tc \/ is_TcRefInt tc} ->
   hst : styping empty (TArr targ cbody) t ->
   hv : validity empty (teqtype t (TConst tc)) ->
   Tot (tb_inversion_res e tc)
let tb_inversion_empty_helper e targ cbody t tc hst hv =
  let Conj hktarr hk = styping_derived #empty #(TArr targ cbody) #t hst in
  let hv : validity empty (teqtype (TArr targ cbody) (TConst tc)) = tb_inversion_styping' #(TArr targ cbody) #t #tc hst hv in
  let hvnot : validity empty (tnot (teqtype (TArr targ cbody) (TConst tc))) = VDistinctTH #empty #(TArr targ cbody) #(TConst tc) hktarr (kdg_tb empty tc) in
   let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype (TArr targ cbody) (TConst tc)) #tfalse hvnot hv in
   empty_consistent hvfalse; TcIntInversion e (TintInversion e 42 Refl)

opaque val tb_inversion_empty : #v:value -> #t:typ -> #wp:typ -> #tc:tconst{is_TcHeap tc \/ is_TcInt tc \/ is_TcRefInt tc} ->
   ht:typing empty v (Cmp EfPure t wp) ->
   hv:validity empty (teqtype t (TConst tc)) ->
   Tot (tb_inversion_res v tc)
(decreases %[ht])
let rec tb_inversion_empty v t wp tc ht hv =
//{{{
match ht with
| TySub #x1 #x2 #c' #c ht' hsc ~>
(
 let Cmp mc typec wpc = c in
 let Cmp mc' typec' wpc' = c' in
 let hst : styping empty typec' typec = SCmp.hs hsc in
 let hv : validity empty (teqtype typec' (TConst tc)) = tb_inversion_styping' #typec' #typec #tc hst hv in
 tb_inversion_empty #v #typec' #wpc' #tc ht' hv
)
| TyRet #x1 #x2 t htot ->
(
 tb_inversion_empty #v #t #(tot_wp t) #tc htot hv
)
| TyConst _ c hwf ->
(
 match c with
 | EcInt i -> if tc = TcInt then TcIntInversion v (TintInversion v i Refl)
              else
	      (
	       let hk : kinding empty (econsts c) KType = kdg_econst empty c hwf in
	       let hvnot : validity empty (tnot (teqtype t (TConst tc))) = VDistinctTH #empty #t #(TConst tc) hk (kdg_tb empty tc) in
	       let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype t (TConst tc)) #tfalse hvnot hv in
	       empty_consistent hvfalse; TcIntInversion v (TintInversion v 42)
	      )
 | EcLoc l -> if tc = TcRefInt then TcRefInversion v (TrefInversion v l Refl)
              else
	      (
	       let hk : kinding empty (econsts c) KType = kdg_econst empty c hwf in
	       let hvnot : validity empty (tnot (teqtype t (TConst tc))) = VDistinctTH #empty #t #(TConst tc) hk (kdg_tb empty tc) in
	       let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype t (TConst tc)) #tfalse hvnot hv in
	       empty_consistent hvfalse; TcIntInversion v (TintInversion v 42 Refl)
	      )
 | EcHeap h -> if tc = TcHeap then TcHeapInversion v (TheapInversion v h Refl)
               else
	       (
	       let hk : kinding empty (econsts c) KType = kdg_econst empty c hwf in
	       let hvnot : validity empty (tnot (teqtype t (TConst tc))) = VDistinctTH #empty #t #(TConst tc) hk (kdg_tb empty tc) in
	       let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype t (TConst tc)) #tfalse hvnot hv in
	       empty_consistent hvfalse; TcIntInversion v (TintInversion v 42 Refl)
	       )
 | EcUnit
 | EcBang
 | EcAssign
 | EcSel
 | EcUpd
 | EcFixPure _ _ _ _
 | EcFixOmega _ _ _ ->(
	       let hk : kinding empty (econsts c) KType = kdg_econst empty c hwf in
	       let hvnot : validity empty (tnot (teqtype t (TConst tc))) = VDistinctTH #empty #t #(TConst tc) hk (kdg_tb empty tc) in
	       let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype t (TConst tc)) #tfalse hvnot hv in
	       empty_consistent hvfalse; TcIntInversion v (TintInversion v 42 Refl)

   )
)
| TyAbs #x1 #targ #ebody m tbody wpbody hktarg htbody ->
(
 let hk : kinding empty (TArr targ (Cmp m tbody wpbody)) KType = let TypingDerived hk _ _ = typing_derived #empty #(ELam targ ebody) #EfPure #(TArr targ (Cmp m tbody wpbody) ) (GEmpty) ht in hk in
 let hvnot : validity empty (tnot (teqtype t (TConst tc))) = VDistinctTH #empty #t #(TConst tc) hk (kdg_tb empty tc) in
 let hvfalse : validity empty tfalse = v_impl_elim #empty #(teqtype t (TConst tc)) #tfalse hvnot hv in
 empty_consistent hvfalse; TcIntInversion v (TintInversion v 42 Refl)
)
| TyApp #x1 #e1 #e2 #x2 #targs1 #tbodys1 #wps1 #wpfuns1 #wpargs1 htfuns1 htargs1 htotargs1 hkargs1 ->
(
 let tarr1 = TArr targs1 (Cmp EfPure tbodys1 wps1) in
 (
  let RemoveSub c1 hsc1 ht' = remove_subtyping #empty #e1 #(Cmp EfPure tarr1 wpfuns1) (GEmpty) htfuns1 in
  let hst1 : styping empty (Cmp.t c1) tarr1 = get_styping_from_scmpex #empty #e1 #c1 #(Cmp EfPure tarr1 wpfuns1) hsc1 in
  match e1 with
  | EConst ec ->
    (
     let TyConst _ _ _ = ht' in
     match ec with
     | EcFixOmega _ _ _
     | EcFixPure _ _ _ _ ->
     (
      (* Partially applied EcFixPure with 1 argument, so its type is a supertype of an arrow. It is too hard to manipulate the type of fixpure so I skip this part. For a more complete proof, see EcUpd. The proof is basically the same *)
      let targ : typ = magic() in
      let cbody : cmp = magic() in
      let hst : styping empty (TArr targ cbody) t = magic() in
      tb_inversion_empty_helper v targ cbody t tc hst hv
     )
     | EcUpd ->
     (
      let StypingInvArr x1 x2 hstarg1 hscbody1 = styping_inversion_arrow_empty #theap #(tot (TArr tref (tot (TArr tint (tot theap))))) #tarr1 hst1 in
      let hst : styping (eextend targs1 empty) (TArr tref (tot (TArr tint (tot theap)))) tbodys1 = SCmp.hs hscbody1 in
      let htotarg : typing empty e2 (tot targs1) = value_inversion_empty #e2 #EfPure #targs1 #wpargs1 htargs1 in
      let hst : styping empty (TArr tref (csubst (sub_elam (sub_ebeta e2)) (tot (TArr tint (tot theap))))) (tsubst_ebeta e2 tbodys1) = styping_substitution (sub_ebeta e2) hst (ebeta_hs #empty #e2 #targs1 htotarg) in
      let targ = tref in
      let cbody = (csubst (sub_elam (sub_ebeta e2)) (tot (TArr tint (tot theap)))) in
      tb_inversion_empty_helper v targ cbody t tc hst hv
     )
     | EcSel ->
     (
      let StypingInvArr x1 x2 hstarg1 hscbody1 = styping_inversion_arrow_empty #theap #(tot (TArr tref (tot tint))) #tarr1 hst1 in
      let hst : styping (eextend targs1 empty) (TArr tref (tot tint)) tbodys1 = SCmp.hs hscbody1 in
      let htotarg : typing empty e2 (tot targs1) = value_inversion_empty #e2 #EfPure #targs1 #wpargs1 htargs1 in
      let hst : styping empty (TArr tref (tot (tint))) (tsubst_ebeta e2 tbodys1) = subst_on_tot (sub_elam (sub_ebeta e2)) tint; styping_substitution (sub_ebeta e2) hst (ebeta_hs #empty #e2 #targs1 htotarg) in
      let targ = tref in
      let cbody = tot tint in
      tb_inversion_empty_helper v targ cbody t tc hst hv
     )
     | EcAssign ->
     (
      let cmpb = cmp_assign (EVar 1) (EVar 0) in
      let StypingInvArr x1 x2 hstarg1 hscbody1 = styping_inversion_arrow_empty #tref #(tot (TArr tint (cmpb))) #tarr1 hst1 in
      let hst : styping (eextend targs1 empty) (TArr tint cmpb) tbodys1 = SCmp.hs hscbody1 in
      let htotarg : typing empty e2 (tot targs1) = value_inversion_empty #e2 #EfPure #targs1 #wpargs1 htargs1 in
      let hst : styping empty (TArr tint (csubst (sub_elam (sub_ebeta e2)) cmpb)) (tsubst_ebeta e2 tbodys1) = styping_substitution (sub_ebeta e2) hst (ebeta_hs #empty #e2 #targs1 htotarg) in
      let targ = tint in
      let cbody = (csubst (sub_elam (sub_ebeta e2)) cmpb) in
      tb_inversion_empty_helper v targ cbody t tc hst hv
     )
    )
  | EApp e11 e12 ~>
  (
   scmpex_efpure #empty #e1 #c1 #(Cmp EfPure tarr1 wpfuns1) hsc1;
   let TyApp #x1 #x2 #x3 #x4 #targs2 #tbodys2 #wps2 #wpfuns2 #wpargs2 htfuns2 htargs2 htotargs2 hktargs2 = ht' in
   let tarr2 = TArr targs2 (Cmp EfPure tbodys2 wps2) in
   let RemoveSub c2 hsc2 ht' = remove_subtyping #empty #e11 #(Cmp EfPure tarr2 wpfuns2) (GEmpty) htfuns2 in
   match e11 with
   | EConst ec11 ->
   (
    match ec11 with
    | EcFixPure tx t' t'' wp ->
    (
      (* It is still the same argument, but it is still too hard to manipulate *)
      let targ : typ = magic() in
      let cbody : cmp = magic() in
      let hst : styping empty (TArr targ cbody) t = magic() in
      tb_inversion_empty_helper v targ cbody t tc hst hv
    )
    | EcUpd ->
    (
     let TyConst _ _ _ = ht' in
     let hst2 = get_styping_from_scmpex #empty #e11 #c2 #(Cmp EfPure tarr2 wpfuns2) hsc2 in
     let StypingInvArr x1 x2 hstarg2 hscbody2 = styping_inversion_arrow_empty #theap #(tot (TArr tref (tot (TArr tint (tot theap))))) #tarr2 hst2 in
     let tarrb = (TArr tref (tot (TArr tint (tot theap)))) in
     let hst : styping (eextend targs2 empty) tarrb tbodys2 = SCmp.hs hscbody2 in
     let htotarg2 : typing empty e12 (tot targs2) = value_inversion_empty #e12 #EfPure #targs2 #wpargs2 htargs2 in
     let lemma : unit -> Lemma (tsubst_ebeta e12 tarrb = tarrb) = magic() in
     (*
     fun x ->
     (
       subst_on_tot (sub_elam (sub_ebeta e12)) (TArr tint (tot theap));
       subst_on_tot (sub_elam (sub_elam (sub_ebeta e12))) theap
       (* SF : this proof should be able to work … *)
     )
     *)
     let hsttemp : styping empty (tarrb) (Cmp.t c1) =
       lemma ();
       styping_substitution (sub_ebeta e12) hst (ebeta_hs #empty #e12 #targs2 htotarg2)
     in
     let hst1 : styping empty tarrb tarr1 =
       SubTrans #empty #(TArr tref (tot (TArr tint (tot (theap))))) #(Cmp.t c1) #tarr1 hsttemp hst1
     in
     let StypingInvArr x1 x2 hstarg1 hscbody1 = styping_inversion_arrow_empty #tref #(tot (TArr tint (tot (theap)))) #tarr1 hst1 in
     let hst : styping (eextend targs1 empty) (TArr tint (tot (theap))) tbodys1 = SCmp.hs hscbody1 in
     let hst : styping empty (TArr tint (tot theap)) (tsubst_ebeta e2 tbodys1) =
       let htotarg1 : typing empty e2 (tot targs1) = value_inversion_empty #e2 #EfPure #targs1 #wpargs1 htargs1 in
       subst_on_tot (sub_elam (sub_ebeta e2)) theap;
       styping_substitution (sub_ebeta e2) hst (ebeta_hs #empty #e2 #targs1 htotarg1)
     in
     let targ = tint in
     let cbody = tot theap in
     tb_inversion_empty_helper v targ cbody t tc hst hv
    )
   )
  )
 )
)
//}}}

opaque val tint_inversion_empty : #v:value -> #wp:typ ->
   ht:typing empty v (Cmp EfPure tint wp) ->
   Tot(tint_inversion_res v)
let tint_inversion_empty v wp ht =
let hv : validity empty (teqtype tint tint) = VEqReflT #empty #tint #KType (kdg_tb empty TcInt) in
let TcIntInversion x1 h = tb_inversion_empty #v #tint #wp #TcInt ht hv in
h

opaque val theap_inversion_empty : #v:value -> #wp:typ ->
   ht:typing empty v (Cmp EfPure theap wp) ->
   Tot(theap_inversion_res v)
let theap_inversion_empty v wp ht =
let hv : validity empty (teqtype theap theap) = VEqReflT #empty #theap #KType (kdg_tb empty TcHeap) in
let TcHeapInversion x1 h = tb_inversion_empty #v #theap #wp #TcHeap ht hv in
h

opaque val tref_inversion_empty : #v:value -> #wp:typ ->
   ht:typing empty v (Cmp EfPure tref wp) ->
   Tot(tref_inversion_res v)
let tref_inversion_empty v wp ht =
let hv : validity empty (teqtype tref tref) = VEqReflT #empty #tref #KType (kdg_tb empty TcRefInt) in
let TcRefInversion x1 h = tb_inversion_empty #v #tref #wp #TcRefInt ht hv in
h


opaque val tysub_derived : #g:env -> #e:exp -> #m:eff -> #t:typ -> #wp:typ -> #t':typ ->
   ht : typing g e (Cmp m t wp) ->
   hst : styping g t t' ->
   Tot (typing g e (Cmp m t' wp))
let tysub_derived g e m t wp t' ht hst = magic()


opaque val pure_progress : #e : exp{not (is_value e)} -> #t:typ -> #wp:typ ->
  ht:typing empty e (Cmp EfPure t wp) ->
  Tot (pure_progress_res e)
(decreases %[ht])

let rec pure_progress e t wp ht =
match ht with
| TySub #x1 #x2 #c' #c ht hsc -> let Cmp mc' tc' wpc' = c' in
    pure_progress #e #tc' #wpc' ht
| TyRet t htot -> pure_progress #e #t #(tot_wp t) htot
| TyIf0 _ eg et ee _ _ wpg wpt wpe htg htt hte ->
(
 if not (is_value eg) then
  let PureProgress eg' hstep = pure_progress #eg #tint #wpg htg in
  PureProgress (EIf0 eg' et ee) (PsIf0E0 #eg #eg' et ee hstep)
 else
 (
  let TintInversion _ i heq = tint_inversion_empty #eg #wpg htg in
  if i = 0 then
    PureProgress (et) (PsIf0 et ee)
  else
    PureProgress (ee) (PsIfS i et ee)
 )
)
| TyApp #x1 #e1 #e2 #x2 #targs #tbodys #wps #wp1s #wp2s ht1 ht2 htot1 hk1 ->
(
 let tarr = TArr targs (Cmp EfPure tbodys wps) in
 if not (is_value e1) then
  let PureProgress e1' hstep = pure_progress #e1 #tarr #wp1s ht1 in
  PureProgress (EApp e1' e2) (PsAppE1 #e1 #e1' e2 hstep)
 else if not (is_value e2) then
  let PureProgress e2' hstep = pure_progress #e2 #targs #wp2s ht2 in
  PureProgress (EApp e1 e2') (PsAppE2 e1 #e2 #e2' hstep)
 else
 (
  let RemoveSub c' hsc ht' = remove_subtyping #empty #e1 #(Cmp EfPure tarr wp1s) (GEmpty) ht1 in
  let hst : styping empty (Cmp.t c') tarr = get_styping_from_scmpex #empty #e1 #c' #(Cmp EfPure tarr wp1s) hsc in
  match e1 with
  | ELam t ebody -> PureProgress (esubst_ebeta e2 ebody) (PsBeta t ebody e2)
  | EConst ec ->
    (
     let TyConst _ _ _ = ht' in
      match stypingd_inversion_arrow #empty #(econsts ec) #targs #(Cmp EfPure tbodys wps) (GEmpty) hst with
       | Inr temp -> (empty_consistent temp; PureProgress (eint 42) (PsIf0 (eint 42) (eint 42)))
       | Inl temp -> (
	 let StypingDInvArr t1 c1 _ hsc = temp in
	 let EcBang = ec in
	 let SCmp m' wp' m wp _ _ _ _ _ _ = hsc in
         PureProgress (eint 42) (PsIf0 (eint 42) (eint 42))
       )
    )
  | EApp e11 e12 ->
  (
   scmpex_efpure #empty #e1 #c' #(Cmp EfPure tarr wp1s) hsc;
   let TyApp #x1 #x2 #x3 #x4 #targs2 #tbodys2 #wps2 #wpfuns2 #wpargs2 htfuns2 htargs2 htotargs2 hktargs2 = ht' in
   let tarr2 = TArr targs2 (Cmp EfPure tbodys2 wps2) in
   let RemoveSub c2 hsc2 ht' = remove_subtyping #empty #e11 #(Cmp EfPure tarr2 wpfuns2) (GEmpty) htfuns2 in
   match e11 with
   | EApp e111 e112 ->
   (
    scmpex_efpure #empty #e11 #c2 #(Cmp EfPure tarr2 wpfuns2) hsc2;
    let TyApp #x1 #x2 #x3 #x4 #targs3 #tbodys3 #wps3 #wpfuns3 #wpargs3 htfuns3 htargs3 htotargs3 hktargs3 = ht' in
    let tarr3 = TArr targs3 (Cmp EfPure tbodys3 wps3) in
    let RemoveSub c3 hsc3 ht' = remove_subtyping #empty #e111 #(Cmp EfPure tarr3 wpfuns3) (GEmpty) htfuns3 in
    let EConst ec111 = e111 in
    match ec111 with
    | EcFixPure tx t' t'' wp ->
    (
     PureProgress (eapp2 e12 e2 (eapp2 (EConst (EcFixPure tx t' t'' wp)) e112 e12)) (PsFixPure tx t' t'' wp e112 e12 e2)
    )
    | EcUpd -> (
      magic()(* SF : works in interaction but not at compilation *)
      (*
      let TyConst _ _ _ = ht' in
      let hst3 : styping empty (econsts EcUpd) tarr3 = get_styping_from_scmpex #empty #e111 #c3 #(Cmp EfPure tarr3 wpfuns3) hsc3 in
      let StypingInvArr x1 x2 hst3 hscbody3 = styping_inversion_arrow_empty #theap #(tot (TArr tref (tot (TArr tint (tot theap))))) #tarr3 hst3 in
      let hst2 : styping empty (TArr tref (tot (TArr tint (tot theap)))) tarr2 =
          let htotarg3 : typing empty e112 (tot targs3) = value_inversion_empty #e112 #EfPure #targs3 #wpargs3 htargs3 in
          let tret3 = Cmp.t c2 in
	  let hst : styping (eextend targs3 empty) (TArr tref (tot (TArr tint (tot theap)))) tbodys3 = SCmp.hs hscbody3 in
          let hsttemp : styping empty (TArr tref (tot (TArr tint (tot theap)))) tret3 = let s = sub_ebeta e112 in subst_on_tot (sub_elam s) (TArr tint (tot theap)); subst_on_tot (sub_elam (sub_elam s)) theap; styping_substitution (sub_ebeta e112) hst (ebeta_hs #empty #e112 #targs3 htotarg3) in
          let hsttemp' : styping empty tret3 tarr2 = get_styping_from_scmpex #empty #e11 #c2 #(Cmp EfPure tarr2 wpfuns2) hsc2 in
          SubTrans #empty #(TArr tref (tot (TArr tint (tot theap)))) #tret3 #tarr2 hsttemp hsttemp'
      in
      let StypingInvArr x1 x2 hst2 hscbody2 = styping_inversion_arrow_empty #tref #(tot (TArr tint (tot (theap)))) #tarr2 hst2 in
      let htotarg2 : typing empty e12 (tot targs2) = value_inversion_empty #e12 #EfPure #targs2 #wpargs2 htargs2 in
      let hst1 : styping empty (TArr tint (tot theap)) tarr =
        let tret2 = Cmp.t c' in
	let hsttbody : styping (eextend targs2 empty) (TArr tint (tot theap)) tbodys2 = SCmp.hs hscbody2 in
        let hsttemp : styping empty (TArr tint (tot theap)) tret2 = subst_on_tot (sub_elam (sub_ebeta e12)) theap; styping_substitution (sub_ebeta e12) hsttbody (ebeta_hs #empty #e12 #targs2 htotarg2) in
	SubTrans #empty #(TArr tint (tot theap)) #tret2 #tarr hsttemp hst
      in
      let StypingInvArr x1 x2 hst1 _ = styping_inversion_arrow_empty #tint #(tot theap) #tarr hst1 in
      let htarg1 : typing empty e2 (Cmp EfPure tint wp2s) =
	tysub_derived #empty #e2 #EfPure #targs #wp2s #tint ht2 hst1 in
      let htarg2 : typing empty e12 (Cmp EfPure tref wpargs2) =
	tysub_derived #empty #e12 #EfPure #targs2 #wpargs2 #tref htargs2 hst2
      in
      let htarg3 : typing empty e112 (Cmp EfPure theap wpargs3) =
	tysub_derived #empty #e112 #EfPure #targs3 #wpargs3 #theap htargs3 hst3
      in
      let TheapInversion _ h heqh = theap_inversion_empty #e112 #(wpargs3) htarg3 in
      let TrefInversion _ l heql = tref_inversion_empty #e12 #(wpargs2) htarg2 in
      let TintInversion _ i heqi = tint_inversion_empty #e2 #(wp2s) htarg1 in
      PureProgress (eheap (upd_heap l i h)) (PsUpd h l i)
      *)
    )
   )
   | EConst ec11 ->
   (
    match ec11 with
    | EcFixOmega tx t' wp ->
    (
     magic()(*
     let TyConst _ _ _ = ht' in
     let hst2 : styping empty (econsts (EcFixOmega tx t' wp)) tarr2 = get_styping_from_scmpex #empty #e11 #c2 #(Cmp EfPure tarr2 wpfuns2) hsc2 in
     let StypingInvArr x1 x2 hst2 hscbody2 = styping_inversion_arrow_empty #(tfixomegaF tx t' wp) #(tot (tfixomegat tx t' wp)) #tarr2 hst2 in
     let hst1 : styping empty (TArr tx (Cmp EfAll (TEApp (tesh t') (EVar 0)) (TEApp (tesh wp) (EVar 0)))) tarr =
       let tret2 = Cmp.t c' in
       let hsttbody : styping (eextend targs2 empty) (tfixomegat tx t' wp) tbodys2 = SCmp.hs hscbody2 in
       let htot2 : typing empty e12 (tot targs2) = value_inversion_empty #e12 #EfPure #targs2 #wpargs2 htargs2 in
       let lemma2 : unit -> Lemma (csubst (sub_elam (sub_ebeta e12)) (tfixomegatret tx t' wp) = Cmp EfAll (TEApp (tesh t') (EVar 0)) (TEApp (tesh wp) (EVar 0))) = magic() in
       let hsttemp : styping empty (TArr tx (Cmp EfAll (TEApp (tesh t') (EVar 0)) (TEApp (tesh wp) (EVar 0)))) tret2 = tsubst_ebeta_shift e12 tx; lemma2 (); styping_substitution (sub_ebeta e12) (hsttbody) (ebeta_hs #empty #e12 #targs2 htot2) in
       SubTrans #empty #(TArr tx (Cmp EfAll (TEApp (tesh t') (EVar 0)) (TEApp (tesh wp) (EVar 0)))) #tret2 #tarr hsttemp hst
     in
     let StypingInvArr x1 x2 hst1 hscbody1 = styping_inversion_arrow_empty #tx #(Cmp EfAll (TEApp (tesh t') (EVar 0)) (TEApp (tesh wp) (EVar 0))) #tarr hst1 in
     let SCmp x1 x2 x3 x4 _ _ _ _ _ _ = hscbody1 in
     PureProgress (eint 42) (PsIf0 (eint 42) (eint 42))
     *)
    )
    | EcSel ->
    (
     magic()(*
     let TyConst _ _ _ = ht' in
     let hst2 : styping empty (econsts (EcSel)) tarr2 = get_styping_from_scmpex #empty #e11 #c2 #(Cmp EfPure tarr2 wpfuns2) hsc2 in
     let StypingInvArr x1 x2 hst2 hscbody2 = styping_inversion_arrow_empty #(theap) #(tot (TArr tref (tot tint))) #tarr2 hst2 in
     let hst1 : styping empty (TArr tref (tot tint)) tarr =
       let tret2 = Cmp.t c' in
       let hsttbody : styping (eextend targs2 empty) (TArr tref (tot (tint))) tbodys2 = SCmp.hs hscbody2 in
       let htot2 : typing empty e12 (tot targs2) = value_inversion_empty #e12 #EfPure #targs2 #wpargs2 htargs2 in
       let lemma2 : unit -> Lemma (tsubst (sub_ebeta e12) (TArr tref (tot (tint))) = TArr tref (tot tint)) = fun _ -> subst_on_tot (sub_elam (sub_ebeta e12)) tint in
       let hsttemp : styping empty (TArr tref (tot (tint))) tret2 = lemma2 (); styping_substitution (sub_ebeta e12) (hsttbody) (ebeta_hs #empty #e12 #targs2 htot2) in
       SubTrans #empty #(TArr tref (tot (tint))) #tret2 #tarr hsttemp hst
     in
     let StypingInvArr x1 x2 hst1 hscbody1 = styping_inversion_arrow_empty #tref #(tot (tint)) #tarr hst1 in
     let htheap : typing empty e12 (Cmp EfPure theap wpargs2) =
       tysub_derived #empty #e12 #EfPure #targs2 #wpargs2 #theap htargs2 hst2
     in
     let htref : typing empty e2 (Cmp EfPure tref wp2s) =
       tysub_derived #empty #e2 #EfPure #targs #wp2s #tref ht2 hst1
     in
     let TrefInversion x2 l heql = tref_inversion_empty #e2 htref in
     let TheapInversion x1 h heqh = theap_inversion_empty #e12 #wpargs2 htheap in
     PureProgress (eint (h l)) (PsSel h l)
     *)
    )
    | EcAssign ->
    (
     magic()(*
     let TyConst _ _ _ = ht' in
     let hst2 : styping empty (econsts EcAssign) tarr2 = get_styping_from_scmpex #empty #e11 #c2 #(Cmp EfPure tarr2 wpfuns2) hsc2 in
     let StypingInvArr x1 x2 hst2 hscbody2 = styping_inversion_arrow_empty #tref #(tot (TArr tint (cmp_assign (EVar 1) (EVar 0)))) #tarr2 hst2 in
     let hst1 : styping empty (TArr tint (cmp_assign e12 (EVar 0))) tarr =
       let tret2 = Cmp.t c' in
       let hsttbody : styping (eextend targs2 empty) (TArr tint (cmp_assign (EVar 1) (EVar 0))) tbodys2 = SCmp.hs hscbody2 in
       let htot2 : typing empty e12 (tot targs2) = value_inversion_empty #e12 #EfPure #targs2 #wpargs2 htargs2 in
       let lemma2 : unit -> Lemma (csubst (sub_elam (sub_ebeta e12)) (cmp_assign (EVar 1) (EVar 0)) = cmp_assign e12 (EVar 0)) = magic() in
       let hsttemp : styping empty (TArr tint (cmp_assign e12 (EVar 0))) tret2 = lemma2 (); styping_substitution (sub_ebeta e12) (hsttbody) (ebeta_hs #empty #e12 #targs2 htot2) in
       SubTrans #empty #(TArr tint (cmp_assign e12 (EVar 0))) #tret2 #tarr hsttemp hst
     in
     let StypingInvArr x1 x2 hst1 hscbody1 = styping_inversion_arrow_empty #tint #(cmp_assign e12 (EVar 0)) #tarr hst1 in
     let SCmp x1 x2 x3 x4 _ _ _ _ _ _ = hscbody1 in
     PureProgress (eint 42) (PsIf0 (eint 42) (eint 42))
     *)
    )
   )
  )
 )
)
