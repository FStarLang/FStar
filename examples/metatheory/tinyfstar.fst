(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module TinyFStar

(********************************************************)
(* Syntax *)
(********************************************************)
type var = nat    // de Bruijn indices
type loc = nat    // global location names

type tconst = 
  | TcUnit
  | TcInt
  | TcRefInt
  | TcHeap
  | TcForall
  | TcAnd
  | TcImp
  | TcNeg
  | TcEq
  | TcTrue
  | TcForallPostPure
  | TcForallPostSt
  | TcEqT
  | TcPrecedes

type econst =
  | EcUnit
  | EcInt : int -> econst
  | EcLoc : loc -> econst
  | EcBang
  | EcAssign
  | EcSel
  | EcUpd

type knd =
  | KType : knd
  | KTArr : t:typ -> k:knd -> knd     (* x:t  bound in k *)
  | KKArr : k1:knd -> k2:knd -> knd   (* a:k1 bound in k2 *)

and typ =
  | TVar   : a:var   -> typ
  | TConst : c:tconst -> typ
  | TArr   : t:typ   -> c:cmp  -> typ (* x:t  bound in c *)
  | TTApp  : t1:typ  -> t2:typ -> typ
  | TEApp  : t:typ   -> e:exp  -> typ
  | TTLam  : k:knd   -> t:typ  -> typ (* a:k  bound in t *)
  | TELam  : t1:typ  -> t2:typ -> typ (* x:t1 bound in t2 *)

and cmp = (* CH: factor out commonality? *)
  | CPure : t:typ -> wp:typ -> cmp
  | CSt   : t:typ -> wp:typ -> cmp

and exp =
  | EVar   : x:var   -> exp
  | EConst : c:econst -> exp
  | ELam   : t:typ   -> e:exp -> exp            (* x:t bound in e *)
  | EApp   : e1:exp  -> e2:exp -> exp
  | ELet   : t:typ   -> e1:exp -> e2:exp -> exp (* x:t bound in e2 *)
  (* CH: if I remember correctly let was to simulate the other contexts?
     Is this part of the language or not? I don't see why we would need it.
     It also doesn't appear in the txt. 

     NS: It appears in the S.R proof in the .txt. 
         There, it is much easier to have one context rule and one place to think about bind.
         So, it's addition is actually a simplification that we might consider using here also.

     CH: I don't understand what this would mean formally.
         Would we be switching to ANF? What about strong reduction?
     CH: Looking at the typing rules in this file (but not the ones
         in the txt!) I'm starting to see what you mean. You want lets
         to be used only for sequencing effects, but not for replacing
         evaluation contexts / switching to ANF, right?
         In any case, we should decide either way, and make this
         and the txt file consistent.
     CH: After having another look, the gain from the let doesn't seem
         so big, it only saves us 3 binds (2 in EApp and 1 in EIf0).
         Is that really worth the pain? *)

  | EIf0   : e0:exp  -> e1:exp -> e2:exp -> exp
  | EFix   : ed:(option exp) -> t:typ  -> e:exp  -> exp
             (* x:(TArr.t t) and then f:t bound in e; 
                i.e. from e index 0 points to x and index 1 to f *)

let mk_eqt t1 t2 = TTApp (TTApp (TConst TcEqT) t1) t2

let t_prec e1 e2 = TEApp (TEApp (TConst TcPrecedes) e1) e2

(********************************************************)
(* Substitutions and de Bruijn index manipulations      *)
(********************************************************)

(* TODO: finish this up
   CH: try to reuse parallel substitution style from lambda_omega *)

(*
 * TODO: AR: in λω, we use distinct de bruijn indices for types and terms, i.e.
 * the typing environment is split for types and terms. when one is extended,
 * lookup domain of the other need not change (the looked up value has to shifted
 * though). this had the advantage
 * that reasoning about (y - 1) when looking for y was a bit simpler. but there we
 * did not have TELam. one way would be to extend tsubst in λω so that when
 * passing a TELam, it *does not* increment the (type) index to be substituted. if
 * we do so, we would need to change the below (and at other places) to be
 * TEApp (TVar 0) (EVar 0).
 * 
 * another change we would need to do is to shift_up types and kinds on extend
 * more uniformly than λω.
 *)
(* CH: I don't think your splitting tricks from LambdaOmega will work
       here, and that's mostly because of KTArr (dependent kinds): now
       kinds depend on the value environment, so there is no
       productive way of splitting the environment. I've tried to tell
       you about this before you applied the splitting tricks to
       LambdaOmega, but you didn't listen, which did make LambdaOmega
       a bit easier, I don't deny that, but it also made it less
       reusable here. A priori, I think that going with only one
       numbering for the bindings + a single environment (as Nik
       already wrote things here) mixed with parallel substitutions
       (separate for substituting expressions and types, they seem
       hard to mix without getting partial or without some dependent
       types trick) is the best way to go for TinyF*. *)
(* CH: In this case, the substitution functions would be more complex
       than if we used distinct deBruijn indices, but having one
       unified typing environment seems be simpler, than having 2
       separate but very much interacting ones. *)

(* AR: Not sure. The "trick" should work here too, we will additionally need to
 * shift the kinds for the type variables env when we add a binding
 * in term variable env (like we currently do in lambda-omega for types
 * in the term variables env). As far as the reuse goes, even if we had taken
 * one numbering approach, we would have to change it substantially
 * to account for dependent kinds (KTArr and KKArr both were missing in
 * lambda-omega), so I am not sure if using unified indices
 * would have made reuse easier. On interactions,
 * in separate indices approach the interactions are only in shifting the
 * ranges of the environments, which we have done in lambda-omega
 * for types.
 * 
 * Having said that, if you think unified indices will be simpler, I am
 * game for trying that out.
 *)


type subst =
  | EForX : e:exp -> x:var -> subst
  | TForA : t:typ -> a:var -> subst

assume val bump_knd' : var -> var -> k:knd -> Tot knd (decreases k)
assume val bump_cmp': var -> var -> c:cmp -> Tot cmp (decreases c)
assume val bump_exp' : var -> var -> e:exp -> Tot exp (decreases e)

val bump_typ' : m:var -> n:var -> t:typ -> Tot typ (decreases t)
let rec bump_typ' m n t = match t with
  | TVar a      -> if a >= m then TVar (a + n) else t
  | TConst c    -> t
  | TArr  t1 c2 -> TArr  (bump_typ' m n t1) (bump_cmp' (m + 1) n c2)
  | TTApp t1 t2 -> TTApp (bump_typ' m n t1) (bump_typ' m n t2)
  | TEApp t1 e2 -> TEApp (bump_typ' m n t1) (bump_exp' m n e2)
  | TTLam k1 t2 -> TTLam (bump_knd' m n k1) (bump_typ' (m + 1) n t2)
  | TELam  t1 t2 -> TELam  (bump_typ' m n t1) (bump_typ' (m + 1) n t2)

let bump_knd n t = bump_knd' 0 n t
let bump_typ n t = bump_typ' 0 n t
let bump_exp n t = bump_exp' 0 n t
let bump_cmp n t = bump_cmp' 0 n t

val bump_subst: subst -> Tot subst
let bump_subst = function
  | EForX e x -> EForX (bump_exp 1 e) (x + 1)
  | TForA t a -> TForA (bump_typ 1 t) (a + 1)

assume val subst_exp: subst -> e:exp -> Tot exp (decreases e)
assume val subst_cmp: subst -> c:cmp -> Tot cmp (decreases c)
val subst_knd: subst -> k:knd -> Tot knd (decreases k)
val subst_typ: subst -> t:typ -> Tot typ (decreases t)

let rec subst_knd (s:subst) (k:knd) = match k with
  | KType -> KType
  | KTArr t1 k2 -> KTArr (subst_typ s t1)
                         (subst_knd (bump_subst s) k2)
  | KKArr k1 k2 -> KKArr (subst_knd s k1)
                         (subst_knd (bump_subst s) k2)

and subst_typ s t = match t with
  | TVar a ->
    begin match s with
      | TForA t' b -> if b=a then t' else t
      | _ -> t
    end
  | TConst _ -> t
  | TArr  t1 c2 -> TArr  (subst_typ s t1) (subst_cmp (bump_subst s) c2)
  | TTApp t1 t2 -> TTApp (subst_typ s t1) (subst_typ s t2)
  | TEApp t1 e2 -> TEApp (subst_typ s t1) (subst_exp s e2)
  | TTLam k1 t2 -> TTLam (subst_knd s k1) (subst_typ (bump_subst s) t2)
  | TELam  t1 t2 -> TELam  (subst_typ s t1) (subst_typ (bump_subst s) t2)

(********************************************************)
(* Reduction for types and pure expressions             *)
(********************************************************)

(* Values *)

val is_value : exp -> Tot bool
let is_value e =
  match e with
  | EVar _
  | EConst _
  | ELam _ _
  | EFix _ _ _ -> true
  | EApp _ _
  | ELet _ _ _
  | EIf0 _ _ _ -> false

type value = e:exp{is_value e}

type heap = loc -> Tot value

(* Contexts *)

type ectx_ehole =
  | CeeTop : ectx_ehole
  | CeeAppL : e2:exp -> ectx_ehole
  | CeeAppR : e1:value -> ectx_ehole
  | CeeIf0 : e1:exp -> e2:exp -> ectx_ehole

val plug_e_in_e : e:exp -> ee:ectx_ehole -> Tot exp
let plug_e_in_e e ee =
  match ee with
  | CeeTop -> e
  | CeeAppL e2 -> EApp e e2
  | CeeAppR e1 -> EApp e1 e
  | CeeIf0 e1 e2 -> EIf0 e e1 e2

type ectx_thole =
  | CetLam : e:exp -> ectx_thole
  | CetFix : ed:(option exp) -> e:exp -> ectx_thole

val plug_t_in_e : t:typ -> et:ectx_thole -> Tot exp
let plug_t_in_e t et =
  match et with
  | CetLam e -> ELam t e
  | CetFix ed e -> EFix ed t e

type cctx =
  | CcPureT : wp:typ -> cctx
  | CcPureWP : t:typ -> cctx
  | CcStT : wp:typ -> cctx
  | CcStWP : t:typ -> cctx

type tctx_thole =
  | CttTop : tctx_thole
  | CttArrT : c:cmp -> tctx_thole
  | CttArrC : t:typ -> cc:cctx -> tctx_thole
  | CttTAppL : t2:typ -> tctx_thole
  | CttTAppR : t1:typ -> tctx_thole
  | CttEApp : e:exp -> tctx_thole
  | CttTLam : k:knd -> tctx_thole
  | CttELam1 : t2:typ -> tctx_thole
  | CttELam2 : t1:typ -> tctx_thole

val plug_t_in_t : t:typ -> tt:tctx_thole -> Tot typ
let plug_t_in_t t tt =
  match tt with
  | CttTop -> t
  | CttArrT c -> TArr t c
  | CttArrC t1 (CcPureT wp) -> TArr t1 (CPure t wp)
  | CttArrC t1 (CcPureWP t2) -> TArr t1 (CPure t2 t)
  | CttArrC t1 (CcStT wp) -> TArr t1 (CSt t wp)
  | CttArrC t1 (CcStWP t2) -> TArr t1 (CSt t2 t)
  | CttTAppL t2 -> TTApp t t2
  | CttTAppR t1 -> TTApp t1 t
  | CttEApp e -> TEApp t e
  | CttTLam k -> TTLam k t
  | CttELam1 t2 -> TELam t t2
  | CttELam2 t1 -> TELam t1 t

(* CH: rather degenerate case, consider inlining in rules *)
type tctx_ehole =
  | CteEApp : t:typ -> tctx_ehole

(* 
   NS: I wonder if formalizing it with contexts is more 
       pain than gain. It is certainly more convenient in the .txt
       to use contexts. But, perhaps it is more prudent to 
       simply do it without contexts here ... not sure. 
  
   CH: In the tctx_ehole case a small pain,
       in the other 2 cases I expect a big gain
*)
val plug_e_in_t : e:exp -> te:tctx_ehole -> Tot typ
let plug_e_in_t e te =
  match te with
  | CteEApp t -> TEApp t e

(* Reduction of types and pure expressions *)

type tstep : typ -> typ -> Type =
  | TsEBeta : tx:typ ->
              t:typ ->
              e:exp ->
              tstep (TEApp (TELam tx t) e) (subst_typ (EForX e 0) t)
  | TsTBeta : k:knd ->
              t:typ ->
              t':typ ->
              tstep (TTApp (TTLam k t) t') (subst_typ (TForA t' 0) t)
  | TsTCtx : tt:tctx_thole ->
             #t:typ ->
             #t':typ ->
             tstep t t' ->
             tstep (plug_t_in_t t tt) (plug_t_in_t t' tt)
  | TsECtx : te:tctx_ehole ->
             #e:exp ->
             #e':exp ->
             epstep e e' ->
             tstep (plug_e_in_t e te) (plug_e_in_t e' te)
and epstep : exp -> exp -> Type =
  | EpsIf0 : e1:exp ->
             e2:exp ->
             epstep (EIf0 (EConst (EcInt 0)) e1 e2) e1
  | EpsIfS : i:int{i<>0} ->
             e1:exp ->
             e2:exp ->
             epstep (EIf0 (EConst (EcInt i)) e1 e2) e2
  | EpsBeta : t:typ ->
              e:exp ->
              v:value ->
              e':exp ->
              epstep (EApp (ELam t e) v) (subst_exp (EForX v 0) e)
  | EpsFix : ed:option exp ->
             t:typ ->
             e:exp ->
             v:value ->
             epstep (EApp (EFix ed t e) v)
               (subst_exp (EForX (EFix ed t e) 0) (subst_exp (EForX v 0) e))
  | EpsECtx : ee:ectx_ehole ->
              #e:exp ->
              #e':exp ->
              epstep e e' ->
              epstep (plug_e_in_e e ee) (plug_e_in_e e' ee)
  | EpsTCtx : et:ectx_thole ->
              #t:typ ->
              #t':typ ->
              tstep t t' ->
              epstep (plug_t_in_e t et) (plug_t_in_e t' et)


(********************************************************)
(* The signatures of Pure and ST and other Monad ops    *)
(********************************************************)
let k_pre_pure    = KType
let k_post_pure t = KTArr t KType
let k_pure t      = KKArr (k_post_pure t) k_pre_pure

let k_pre_st      = KTArr (TConst TcHeap) KType
let k_post_st t   = KTArr t (KTArr (TConst TcHeap) KType)
let k_st t        = KKArr (k_post_st t) k_pre_st

let tot t = CPure t (TTLam (k_post_pure t)
                      (TTApp (TTApp (TConst TcForall) t)
                         (TELam t (TEApp (TVar 1) (EVar 0)))))

val bind_pure:  c1:cmp{is_CPure c1}
             -> c2:cmp{is_CPure c2}
             -> Tot cmp
let bind_pure (CPure t1 wp1) (CPure t2 wp2) = (* bind wp1 wp2 post = wp1 (fun (x:t1) -> wp2 x post) *)
  let wp2 = TELam t1 wp2 in
  CPure t2 (TTLam (* post *)
              (k_post_pure t2)  (* don't need to bump t2, since we'll have a side condition ensuring that x:t1 not free in t2 *)
                                (* AR: we are putting t2 under a TTLam, so don't we need to shift it up ? For example if t2
                                   is the type variable 0, we need to make it 1 now ? *)
              (TTApp (bump_typ 1 wp1)
                 (TELam (* x *)
                    (bump_typ 1 t1)
                    (TTApp
                       (TEApp (bump_typ 2 wp2) (EVar 0))
                       (TVar 1)))))


val lift_pure_st : c1:cmp{is_CPure c1}
                -> Tot cmp
let lift_pure_st (CPure t wp) =
  CSt t (TTLam (* post *)
           (k_post_st t)
           (TELam (* h *)
              (TConst TcHeap)
              (TTApp (bump_typ 2 wp)
                 (TELam (* x *)
                    t
                    (TEApp (TEApp (TVar 2) (*post*) (EVar 0) (*x*)) (EVar 1)(*h*))))))

val bind_st:  c1:cmp{is_CSt c1}
           -> c2:cmp{is_CSt c2}
           -> Tot cmp
let bind_st (CSt t1 wp1) (CSt t2 wp2) =
  let wp2 = TELam t1 wp2 in
  CSt t2 (TTLam (* post *)
              (k_post_st t2)  (* don't need to bump t2, since we'll have a side condition ensuring that x:t1 not free in t2 *)
              (TTApp (bump_typ 1 wp1)
                 (TELam (* x *)
                    (bump_typ 1 t1)
                    (TTApp
                       (TEApp (bump_typ 2 wp2) (EVar 0))
                       (TVar 1)))))

val bind: c1:cmp -> c2:cmp -> Tot cmp
let bind c1 c2 = match c1, c2 with
  | CPure _ _, CPure _ _ -> bind_pure c1 c2
  | CSt _ _,   CSt _ _   -> bind_st   c1 c2
  | CSt _ _,   CPure _ _ -> bind_st   c1 (lift_pure_st c2)
  | CPure _ _, CSt _ _   -> bind_st   (lift_pure_st c1) c2

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

let mk_eq t e1 e2      = TEApp (TEApp (TTApp (TConst TcEq) t) e1) e2
let neg phi            = TTApp (TConst TcNeg) phi

val bind_pure_if : exp -> c1:cmp{is_CPure c1} -> c2:cmp{is_CPure c2} -> Tot cmp
let bind_pure_if e (CPure t wp1) (CPure _ wp2) =
  let guard = mk_eq (TConst TcInt) e (EConst (EcInt 0)) in
  let wp = op_CPure t (TConst TcAnd) (op_CPure t (TConst TcImp) (up_CPure t guard) wp1) (op_CPure t (TConst TcImp) (up_CPure t (neg guard)) wp2) in
  CPure t wp

val bind_st_if : exp -> c1:cmp{is_CSt c1} -> c2:cmp{is_CSt c2} -> Tot cmp
let bind_st_if e (CSt t wp1) (CSt _ wp2) =
  let guard = mk_eq (TConst TcInt) e (EConst (EcInt 0)) in
  let wp = op_CSt t (TConst TcAnd) (op_CSt t (TConst TcImp) (up_CSt t guard) wp1) (op_CSt t (TConst TcImp) (up_CSt t (neg guard)) wp2) in
  CSt t wp

val bind_if : exp -> cmp -> cmp -> Tot cmp
let bind_if e c1 c2 = match c1, c2 with
  | CPure _ _, CPure _ _ -> bind_pure_if e c1 c2
  | CPure _ _, CSt _ _   -> bind_st_if e (lift_pure_st c1) c2
  | CSt _ _, CPure _ _   -> bind_st_if e c1 (lift_pure_st c2)
  | CSt _ _, CSt _ _     -> bind_st_if e c1 c2

let result_typ = function
  | CPure t _
  | CSt t  _   -> t

let set_result_typ c t = match c with
  | CPure _ wp ->  CPure t wp
  | CSt _ wp -> CSt t wp

(********************************************************)
(* Signature for constants                              *)
(********************************************************)

val tconsts : tconst -> Tot knd
let tconsts tc =
  match tc with
  | TcUnit   -> KType
  | TcInt    -> KType
  | TcRefInt -> KType
  | TcHeap   -> KType
  | TcForall -> KKArr KType (KKArr (KTArr (TVar 0) KType) KType)
                (* TODO: please double-check *)
  | TcAnd
  | TcImp
  | TcEqT    -> KKArr KType (KKArr KType KType)
                (* TODO: please double-check (for TcEqT) *)
  | TcNeg    -> KKArr KType KType
  | TcEq
  | TcPrecedes -> KKArr KType (KTArr (TVar 0) (KTArr (TVar 0) KType))
                 (* TODO: please double-check *)

  | TcTrue   -> KType
  | TcForallPostPure 
  | TcForallPostSt -> KType (* TODO: finish this *)

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

(********************************************************)
(* Typing environments *)
(********************************************************)

type var_binding =
  | B_a : k:knd -> var_binding
  | B_x : t:typ -> var_binding
type env = var -> Tot (option var_binding)

val extend: env -> var_binding -> Tot env
let extend env var_binding = function
  | 0 -> Some var_binding
  | i ->
    match env (i - 1) with
      | None -> None
      | Some (B_a k) -> Some (B_a (bump_knd 1 k))
      | Some (B_x t) -> Some (B_x (bump_typ 1 t))

val empty : env
let empty x = None

val binds: test:(var_binding -> Tot bool) -> env -> var -> Tot bool
let binds test g x = match g x with
  | Some b -> test b
  | _ -> false

let binds_a   = binds is_B_a
let binds_x   = binds is_B_x

val lookup: a:Type
         -> test:(var_binding -> Tot bool)
         -> g:env
         -> x:var{binds test g x}
         -> project:(b:var_binding{test b} -> Tot a)
         -> Tot a
let lookup test g x project = let Some b = g x in project b

let lookup_a    g a = lookup is_B_a g a B_a.k
let lookup_x    g x = lookup is_B_x g x B_x.t

(********************************************************)
(* Main typing judgments *)
(********************************************************)

type sub_cmp : env -> cmp -> cmp -> typ -> Type =
  | SubLift : g:env
           -> c:cmp{is_CPure c}
           -> sub_cmp g c (lift_pure_st c) (TConst TcTrue)

  | SubPure : g:env
           -> t:typ
           -> wp1:typ
           -> wp2:typ
           -> sub_cmp g (CPure t wp1) (CPure t wp2)
                      (down_CPure t (op_CPure t (TConst TcImp) wp2 wp1))

  | SubST   : g:env
           -> t:typ
           -> wp1:typ
           -> wp2:typ
           -> sub_cmp g (CSt t wp1) (CSt t wp2)
                      (down_CSt t (op_CSt t (TConst TcImp) wp2 wp1))

  | SubRes : g:env
          -> c:cmp
          -> t:typ
          -> phi:typ
          -> sub_typ g (result_typ c) t phi
          -> sub_cmp g c (set_result_typ c t) phi

and sub_typ : env -> typ -> typ -> typ -> Type =
  | SubTRefl: g:env
           -> t:typ
           -> sub_typ g t t (TConst TcTrue)

  | SubTArr: g:env
           -> t1:typ
           -> t2:typ
           -> c1:cmp
           -> c2:cmp
           -> phi1:typ
           -> phi2:typ
           -> sub_typ g t2 t1 phi1
           -> sub_cmp (extend g (B_x t2)) c1 c2 phi2
           -> sub_typ g (TArr t1 c1) (TArr t2 c2)
                      (conj phi1 (close_forall t2 phi2))

(* AR: adding it *)
assume val asHeap: heap -> Tot exp

(* generic function on functional maps, should be in library *)
val upd_heap : l:loc -> v:value -> h:heap -> Tot heap
let upd_heap l v h l' = if l = l' then v else h l'

(* CH: try to enable the use of SMT automation as much as possible,
       otherwise we will die building huge derivations in a low-level
       deduction system.

   NS: Not sure what you mean. Isn't this style similar to λω?

   CH: My comment was about the logical validity judgment, which then
       got moved without it. I think I would prefer if we could write
       valid in shallow embedding style (Tarski semantics), so that we
       can take advantage of SMT automation. Or maybe as a proper
       "logic" inductive? In any case, I've found natural deduction /
       sequent calculus style reasoning highly painful to work with in
       the past, and the logical formulas I see here (in the WPs) are
       an order of magnitude bigger than what I had to work
       with. Maybe we won't need to reason about valid that much,
       because we only prove very syntactic things? Or otherwise
       what's the catch? *)

(* Logical validity reasons about types and pure expression up to
   convertibity / (strong???) reduction *)
type valid: env -> typ -> Type =
    (* AR: .txt has no refl. ? *)
  | VTEqRefl:    #g:env -> #t:typ ->
                 valid g (mk_eqt t t)
  | VTEqTran:    #g:env -> #t:typ -> #t1:typ -> #t2:typ ->
                 valid g (mk_eqt t t1) ->
                 valid g (mk_eqt t t2) ->   
                 valid g (mk_eqt t t2)
    (* CH: Isn't VTApp already part of VTReduction? *)
  | VTApp:       #g:env -> #t1:typ -> #t2:typ ->
                 f:typ ->
                 valid g (mk_eqt t1 t2) ->
                 valid g (mk_eqt (TTApp f t1) (TTApp f t2))
  | VTEqValid:   #g:env -> #t1:typ -> #t2:typ ->
                 valid g (mk_eqt t1 t2) ->
                 valid g t1 ->
                 valid g t2
  | VSelAsHeap:  t:typ -> (* type of the value in heap location *)
                 g:env ->
                 h:heap ->
                 l:loc ->
                 valid g (mk_eq t (EApp (EApp (EConst EcSel) (asHeap h))
                                        (EConst (EcLoc l))) (h l))
  | VUpdAsHeap:  g:env ->
                 h:heap ->
                 l:loc ->
                 v:value ->
                 valid g (mk_eq (TConst TcHeap)
                                (EApp (EApp (EApp (EConst EcUpd) (asHeap h))
                                            (EConst (EcLoc l))) v)
                                (asHeap (upd_heap l v h)))

  (* CH: There are two more sel-upd rules in the txt. What happened to those? *)
  
  (*
   * AR: do we need to add next 2 validity rules
   * sel (upd h l v) = v and the next one.
   * perhaps they can be derived from VSel and VUpd above
   *)
  | VForallT:    #g:env -> #t:typ -> #phi:typ ->
                 valid (extend g (B_x t)) phi ->
                 valid g (close_forall t phi)

  (* AR: TODO: forall with kinds ? *)

  | VForallTElim:#g:env -> #t:typ -> #phi:typ -> #e:exp ->
                 valid g (close_forall t phi) ->
                 typing g e (tot t) ->
                 valid g (subst_typ (EForX e 0) phi) (* AR: careful with shifts *)

  (* AR: TODO: forall elim with kinds ? *)

  | VTReduction: #g:env -> #t:typ -> #t':typ ->
                 tstep t t' ->
                 valid g (mk_eqt t t')
		   
  | VEReduction: #g:env -> t:typ -> #e:exp -> #e':exp ->
                 epstep e e' ->
                 valid g (mk_eq t e e')

   (* CH: TODO: there are a lot more logical constants that have no
          rule here, not just the foralls *)

and typing : env -> exp -> cmp -> Type =
  | TyVar   : #g:env
           -> x:var{binds_x g x}
           -> kinding g (lookup_x g x) KType
           -> typing g (EVar x) (tot (lookup_x g x))

  | TyConst : g:env
           -> c:econst
(* 
           -> kinding g (econsts c) KType
              CH: TODO: prove once and for all that this holds!
*)
           -> typing g (EConst c) (tot (econsts c))

  | TyAbs  : #g:env
          -> #t:typ
          -> #e:exp
          -> #c:cmp
          -> kinding g t KType
          -> typing (extend g (B_x t)) e c
          -> typing g (ELam t e) (tot (TArr t c))

  | TyFix : #g:env
         -> tx:typ
         -> t':typ
         -> wp:typ
         -> #d:exp
         -> #e:exp
         -> kinding g (TArr tx (CPure t' wp)) KType
         -> typing g d (tot (TArr tx (tot t')))
         -> typing (extend (extend g (B_x tx))
                           (B_x (TArr tx (CPure t' (op_CPure t' (TConst TcAnd)
                              (up_CPure t' (t_prec (EApp d (EVar 0))
                                                   (EApp d (EVar 1)))) wp)))))
                   e (CPure t' wp)
         -> typing g (EFix (Some d) (TArr tx (CPure t' wp)) e)
                               (tot (TArr tx (CPure t' wp)))

  | TyFixOmega : #g:env
              -> tx:typ
              -> t':typ
              -> wp:typ
              -> #e:exp
              -> kinding g (TArr tx (CSt t' wp)) KType
              -> typing (extend (extend g (B_x tx)) (B_x (TArr tx (CSt t' wp))))
                        e (CSt t' wp)
              -> typing g (EFix None (TArr tx (CSt t' wp)) e)
                                (tot (TArr tx (CSt t' wp)))

  | TyApp : #g:env
         -> #e1:exp
         -> #e2:exp
         -> #t:typ
         -> #c:cmp
         -> typing g e1 (tot (TArr t c))
         -> typing g e2 (tot t)
         -> typing g (EApp e1 e2) (subst_cmp (EForX e2 0) c)

  | TyLet : #g:env
         -> #e1:exp
         -> #e2:exp
         -> #c1:cmp
         -> #c2:cmp
         -> typing g e1 c1
         -> typing (extend g (B_x (result_typ c1))) e2 c2
         -> kinding g (result_typ c2) KType
         -> typing g (ELet (result_typ c1) e1 e2) (bind c1 c2)

  | TyIf : #g:env
        -> #e0:exp
        -> #e1:exp
        -> #e2:exp
        -> #c1:cmp
        -> #c2:cmp{result_typ c1 = result_typ c2}
        -> typing g e0 (tot (TConst TcInt))
        -> typing g e1 c1
        -> typing g e2 c2
        -> typing g (EIf0 e0 e1 e2) (bind_if e0 c1 c2)

  | TySub: #g:env
        -> #e:exp
        -> #c:cmp
        -> #c':cmp
        -> #phi:typ
        -> typing g e c
        -> sub_cmp g c c' phi
        -> c_ok g c'
        -> valid g phi (* valid includes type conversion *)
        -> typing g e c'

and kinding : env -> typ -> knd -> Type =
  | KiVar   : g:env
           -> a:var{binds_a g a}
           -> kinding g (TVar a) (lookup_a g a)

  | KiConst : g:env
           -> c:tconst
           -> kinding g (TConst c) (tconsts c)

  | KiArr   : #g:env
           -> #t:typ
           -> #c:cmp
           -> kinding g t KType
           -> c_ok (extend g (B_x t)) c
           -> kinding g (TArr t c) KType

  | KiTTApp : #g:env
           -> #t1:typ
           -> #t2:typ
           -> #k1:knd
           -> #k2:knd
           -> kinding g t1 (KKArr k1 k2)
           -> kinding g t2 k1
           -> kinding g (TTApp t1 t2) (subst_knd (TForA t2 0) k2)

  | KiTEApp : #g:env
           -> #t1:typ
           -> #e:exp
           -> #t:typ
           -> #k:knd
           -> kinding g t1 (KTArr t k)
           -> typing g e (tot t)
           -> kinding g (TEApp t1 e) (subst_knd (EForX e 0) k)

  | KiTTLam : #g:env
           -> #k:knd
           -> #t:typ
           -> #k':knd
           -> kind_ok g k
           -> kinding (extend g (B_a k)) t k'
           -> kinding g (TTLam k t) (KKArr k k')

  | KiTELam : #g:env
           -> #t1:typ
           -> #t2:typ
           -> #k:knd
           -> kinding g t1 KType
           -> kinding (extend g (B_x t1)) t2 k
           -> kinding g (TELam t1 t2) (KTArr t1 k)

and c_ok : env -> cmp -> Type =
  | COkPure :  #g:env
            -> #t:typ
            -> #wp:typ
            -> kinding g t KType
            -> kinding g wp (k_pure t)
            -> c_ok g (CPure t wp)

  | COkSt :    #g:env
            -> #t:typ
            -> #wp:typ
            -> kinding g t KType
            -> kinding g wp (k_st t)
            -> c_ok g (CSt t wp)

(* kind_ok needed because (as opposed to LambdaOmega) kinds have
   variable and type bindings *)
and kind_ok : env -> knd -> Type =
  | KOkType : g:env
           -> kind_ok g KType

  | KOkTArr : #g:env
           -> #t:typ
           -> #k:knd
           -> kinding g t KType
           -> kind_ok (extend g (B_x t)) k
           -> kind_ok g (KTArr t k)

  | KOkKArr : #g:env
           -> #k1:knd
           -> #k2:knd
           -> kind_ok g k1
           -> kind_ok (extend g (B_a k1)) k2
           -> kind_ok g (KKArr k1 k2)

(********************************************************)
(* Impure reduction for types and pure expressions      *)
(********************************************************)

type cfg =
  | Cfg : h:heap -> e:exp -> cfg

type eistep : cfg -> cfg -> Type =
  | EisPure : h:heap ->
              #e:exp ->
              #e':exp ->
              epstep e e' ->
              eistep (Cfg h e) (Cfg h e')
  | EisRd : h:heap ->
            l:loc ->
            eistep (Cfg h (EApp (EConst EcBang) (EConst (EcLoc l)))) (Cfg h (h l))
  | EisWr : h:heap ->
            l:loc ->
            v:value ->
            eistep (Cfg h (EApp (EApp (EConst EcAssign) (EConst (EcLoc l))) v))
                   (Cfg (upd_heap l v h) (EConst EcUnit))

(********************************************************)
(* Experiments                                          *)
(********************************************************)

(* (\* AR: without contexts *\) *)

(* type tstepnc: typ -> typ -> Type = *)
(*   | TsTBeta : #k:knd -> *)
(*               #t:typ -> *)
(*               #t':typ -> *)
(*               tstepnc (TTApp (TTLam k t) t') (subst_typ (TForA t' 0) t) *)
(*   | TsEBeta : #tx:typ -> *)
(*               #t:typ -> *)
(*               #e:exp -> *)
(*               tstepnc (TEApp (TELam tx t) e) (subst_typ (EForX e 0) t) *)
(*   | TsTApp_1:  *)
