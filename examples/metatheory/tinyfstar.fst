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
type var = nat    //de Bruijn index
type loc = nat
type const = int  // CH: trying to pack all exp and typ constants
                  // and locations in one int seems very unelegant
                  // (and will need quite a complex encoding, since
                  //  constants include integers and locations are
                  //  also an infinite set) 
                  // NS: What is the alternative? 
                  //     We need constants at multiple levels
type knd =
  | KType : knd
  | KTArr : t:typ -> k:knd -> knd     (* x:t  bound in k *)
  | KKArr : k1:knd -> k2:knd -> knd   (* a:k1 bound in k2 *)

and typ =
  | TVar   : a:var   -> typ
  | TConst : c:const -> typ
  | TArr   : t:typ   -> c:cmp  -> typ (* x:t  bound in c *)
  | TTApp  : t1:typ  -> t2:typ -> typ
  | TEApp  : t:typ   -> e:exp  -> typ
  | TTLam  : k:knd   -> t:typ  -> typ (* a:k  bound in t *)
  | TELam  : t1:typ  -> t2:typ -> typ (* x:t1 bound in t2 *)

and cmp =
  | CPure : t:typ -> wp:typ -> cmp
  | CSt   : t:typ -> wp:typ -> cmp

and exp =
  | EVar   : x:var   -> exp
  | EConst : c:const -> exp
  | ELoc   : l:loc   -> exp (* CH: do we want this, or are they just constants? NS: Yes, we can probably collapse this. *)
  | EInt   : l:int   -> exp (* CH: weren't ints just constants? NS: Yes. But (EInt 0) : int  and (EConst 0) should have some other type depending on the signature *)
  | ELam   : t:typ   -> e:exp -> exp            (* x:t bound in e *)
  | EApp   : e1:exp  -> e2:exp -> exp
  | ELet   : t:typ   -> e1:exp -> e2:exp -> exp (* x:t bound in e2 *)
  (* CH: if I remember correctly let was to simulate the other contexts?
     Is this part of the language or not? I don't see why we would need it.
     It also doesn't appear in the txt. 

     NS: It appears in the S.R proof in the .txt. 
         There, it is much easier to have one context rule and one place to think about bind.
         So, it's addition is actually a simplification that we might consider using here also.
  *)
  | EIf0   : e0:exp  -> e1:exp -> e2:exp -> exp
  | EFix   : ed:(option exp) -> t:typ  -> e:exp  -> exp
             (* f:t and x bound in e *)

(* Constants *)
let t_unit   = TConst 0
let t_int    = TConst 1
let t_refint = TConst 2
let t_heap   = TConst 3
let t_forall = TConst 4
let t_and    = TConst 5
let t_imp    = TConst 6
let t_neg    = TConst 7
let t_eq     = TConst 8
let t_true   = TConst 9

let t_forall_post_pure = TConst 10
let t_forall_post_st   = TConst 11

(* AR: adding it *)
let t_eqt    = TConst 12

let e_bang   = EConst 100
let e_assign = EConst 101
let e_sel    = EConst 102
let e_upd    = EConst 103
let e_unit   = EConst 104

let mk_eqt t1 t2 = TTApp (TTApp t_eqt t1) t2

(* 
   CH: still missing the integer constants. 
   NS: (EInt i) are the integer constants
*)

(********************************************************)
(* Substitutions and de Bruijn index manipulations      *)
(********************************************************)

(* TODO: finish this up
   CH: try to reuse parallel substitution style from lambda_omega *)

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



(* Values *)

val is_value : exp -> Tot bool
let is_value e =
  match e with
  | EVar _
  | EConst _
  | ELoc _
  | EInt _
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
*)
val plug_e_in_t : e:exp -> te:tctx_ehole -> Tot typ
let plug_e_in_t e te =
  match te with
  | CteEApp t -> TEApp t e

(* Reduction in types and pure expressions *)

type tstep : typ -> typ -> Type =
  | TsEBeta : tx:typ ->
              t:typ ->
              e:exp ->
              tstep (TEApp (TELam tx t) e) (subst_typ (EForX e 0) t)
                                    (* TODO: + a shift down actually
                                       (for all the betas and twice for fix) *)
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
             epstep (EIf0 (EInt 0) e1 e2) e1
  | EpsIfS : i:int{i<>0} ->
             e1:exp ->
             e2:exp ->
             epstep (EIf0 (EInt i) e1 e2) e2
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
  | EpsTCtx : et:ectx_thole ->
              #t:typ ->
              #t':typ ->
              tstep t t' ->
              epstep (plug_t_in_e t et) (plug_t_in_e t' et)
    (* CH: Is it really on purpose that this doesn't include a EpsECtx rule?
           How will we get to doing the betas?
           EisECtx won't really help with that

       NS: There is an a E-Ctx rule in the .txt which should cover this.
    *)


(********************************************************)
(* The signatures of Pure and ST and other Monad ops    *)
(********************************************************)
let k_pre_pure    = KType
let k_post_pure t = KTArr t KType
let k_pure t      = KKArr (k_post_pure t) k_pre_pure

let k_pre_st      = KTArr t_heap KType
let k_post_st t   = KTArr t (KTArr t_heap KType)
let k_st t        = KKArr (k_post_st t) k_pre_st

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
let tot t = CPure t (TTLam (k_post_pure t)
                      (TTApp (TTApp t_forall t)
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
              t_heap
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

let conj phi1 phi2        = TTApp (TTApp t_and phi1) phi2

(* AR: do we handle shifting up etc. here for phi ? *)
let close_forall t phi    = TTApp (TTApp t_forall t) (TELam t phi)

let down_CPure t wp       = TTApp (TTApp t_forall_post_pure t)
                                  (TTLam (k_post_pure t) (TTApp (bump_typ 1 wp) (TVar 0)))
let down_CSt t wp         = TTApp (TTApp t_forall_post_st t)
                                  (TTLam (k_post_st t)
                                     (TELam t_heap (TEApp (TTApp (bump_typ 2 wp) (TVar 1)) (EVar 0))))
let up_CPure t phi        = TTLam (k_post_pure t) (bump_typ 1 phi)
let up_CSt   t phi        = TTLam (k_post_st t)   (TELam t_heap (bump_typ 2 phi))
let op_CPure t op wp1 wp2 = TTLam (k_post_pure t) (TTApp (TTApp op
                                                            (TTApp (bump_typ 1 wp1) (TVar 0)))
                                                           (TTApp (bump_typ 1 wp2) (TVar 0)))
let op_CSt t op wp1 wp2   = TTLam (k_post_st t)   (TELam t_heap (TTApp (TTApp op
                                                                         (TEApp (TTApp (bump_typ 2 wp1) (TVar 1)) (EVar 0)))
                                                                  (TEApp (TTApp (bump_typ 2 wp2) (TVar 1)) (EVar 0))))

let mk_eq t e1 e2      = TEApp (TEApp (TTApp t_eq t) e1) e2
let neg phi            = TTApp t_neg phi

val bind_pure_if : exp -> c1:cmp{is_CPure c1} -> c2:cmp{is_CPure c2} -> Tot cmp
let bind_pure_if e (CPure t wp1) (CPure _ wp2) =
  let guard = mk_eq t_int e (EInt 0) in
  let wp = op_CPure t t_and (op_CPure t t_imp (up_CPure t guard) wp1) (op_CPure t t_imp (up_CPure t (neg guard)) wp2) in
  CPure t wp

val bind_st_if : exp -> c1:cmp{is_CSt c1} -> c2:cmp{is_CSt c2} -> Tot cmp
let bind_st_if e (CSt t wp1) (CSt _ wp2) =
  let guard = mk_eq t_int e (EInt 0) in
  let wp = op_CSt t t_and (op_CSt t t_imp (up_CSt t guard) wp1) (op_CSt t t_imp (up_CSt t (neg guard)) wp2) in
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
(* Typing environments *)
(********************************************************)

(* CH: where are the location bindings from the txt? *)
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

type const_binding =
  | B_l : t:typ -> const_binding (* CH: locations bound in signature?
                                        they seem statically allocated (no ref)
                                        (in the txt they are in environment)
                                        (they anyway all have type ref int). 
                                    NS: In this calculus, without dynamic allocation, perhaps it is better 
                                        to have them in the signature rather than the context. 
                                        I don't have a string preference ... we could move B_l to var_binding *)
  | B_c : t:typ -> const_binding
  | B_t : k:knd -> const_binding
type constants = int -> Tot (option const_binding)

val signature : constants
let signature = function
  | 0 -> Some (B_t KType) //t_unit
  | 1 -> Some (B_t KType) //t_int
  | 2 -> Some (B_t KType) //t_refint
  | _ -> None (* TODO: fill this in *)

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

val binds_const: (const_binding -> Tot bool) -> int -> Tot bool
let binds_const test c = match signature c with
  | Some b -> test b
  | _ -> false

let binds_l = binds_const is_B_l
let binds_c = binds_const is_B_c
let binds_t = binds_const is_B_t

val lookup_l: l:int{binds_l l} -> Tot typ
let lookup_l l = B_l.t (Some.v (signature l))

val lookup_c: c:int{binds_c c} -> Tot typ
let lookup_c c = B_c.t (Some.v (signature c))

val lookup_t: t:int{binds_t t} -> Tot knd
let lookup_t t = B_t.k (Some.v (signature t))

(********************************************************)
(* Main typing judgments *)
(********************************************************)

(* TODO: write valid down *)
(* CH: try to enable the use of SMT automation as much as possible,
       otherwise we will die using building huge derivations
       in a low-level deduction system. 

   NS: Not sure what you mean. Isn't this style similar to λω?
 *)

type sub_cmp : env -> cmp -> cmp -> typ -> Type =
  | SubLift : g:env
           -> c:cmp{is_CPure c}
           -> sub_cmp g c (lift_pure_st c) t_true

  | SubPure : g:env
           -> t:typ
           -> wp1:typ
           -> wp2:typ
           -> sub_cmp g (CPure t wp1) (CPure t wp2)
                      (down_CPure t (op_CPure t t_imp wp2 wp1))

  | SubST   : g:env
           -> t:typ
           -> wp1:typ
           -> wp2:typ
           -> sub_cmp g (CSt t wp1) (CSt t wp2)
                      (down_CSt t (op_CSt t t_imp wp2 wp1))

  | SubRes : g:env
          -> c:cmp
          -> t:typ
          -> phi:typ
          -> sub_typ g (result_typ c) t phi
          -> sub_cmp g c (set_result_typ c t) phi

and sub_typ : env -> typ -> typ -> typ -> Type =
  | SubTRefl: g:env
           -> t:typ
           -> sub_typ g t t t_true

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

type valid: env -> typ -> Type =
    (* AR: .txt has no refl. ? *)
  | VTEqRefl:    #g:env -> #t:typ ->
                 valid g (mk_eqt t t)
  | VTEqTran:    #g:env -> #t:typ -> #t1:typ -> #t2:typ ->
                 valid g (mk_eqt t t1) ->
                 valid g (mk_eqt t t2) ->   
                 valid g (mk_eqt t t2)
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
                 valid g (mk_eq t (EApp (EApp e_sel (asHeap h)) (ELoc l)) (h l))
  | VUpdAsHeap:  g:env ->
                 h:heap ->
                 l:loc ->
                 v:value ->
                 valid g (mk_eq t_heap (EApp (EApp (EApp e_upd (asHeap h)) (ELoc l)) v)
                                       (asHeap (upd_heap l v h)))  
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

and typing : env -> exp -> cmp -> Type =
  | TypingLoc   : g:env
               -> l:int{binds_l l /\ lookup_l l = t_refint}
               -> typing g (ELoc l) (tot t_refint)

  | TypingVar   : g:env
               -> x:var{binds_x g x}
               -> kinding g (lookup_x g x) KType
               -> typing g (EVar x) (tot (lookup_x g x))

  | TypingConst : g:env
               -> c:int{binds_c c}
               -> kinding g (lookup_c c) KType
               -> typing g (EConst c) (tot (lookup_c c))

  | TypingAbs  : g:env
              -> t:typ
              -> e:exp
              -> c:cmp
              -> kinding g t KType
              -> typing (extend g (B_x t)) e c
              -> typing g (ELam t e) (tot (TArr t c))

  | TypingApp :  g:env
             -> e1:exp
             -> e2:exp
             -> tarr:typ{is_TArr tarr}
             -> typing g e1 (tot tarr)
             -> typing g e2 (tot (TArr.t tarr))
             -> typing g (EApp e1 e2) (subst_cmp (EForX e2 0) (TArr.c tarr))

  | TypingLet : g:env
             -> e1:exp
             -> e2:exp
             -> c1:cmp
             -> c2:cmp
             -> typing g e1 c1
             -> typing (extend g (B_x (result_typ c1))) e2 c2
             -> kinding g (result_typ c2) KType
             -> typing g (ELet (result_typ c1) e1 e2) (bind c1 c2)

  | TypingIf : g:env
            -> e0:exp
            -> e1:exp
            -> e2:exp
            -> c1:cmp
            -> c2:cmp{result_typ c1 = result_typ c2}
            -> typing g e0 (tot t_int)
            -> typing g e1 c1
            -> typing g e2 c2
            -> typing g (EIf0 e0 e1 e2) (bind_if e0 c1 c2)

  | TypingSub: g:env
            -> e:exp
            -> c:cmp
            -> c':cmp
            -> phi:typ
            -> typing g e c
            -> sub_cmp g c c' phi
            -> c_ok g c'
            -> valid g phi
            -> typing g e c'

(* CH: Missing the 2 fix rules (see T-Fix and T-FixOmega in txt) 

   NS: Yes, we should add it. 
*)

(* CH: Where is the type conversion (typing or subtyping) rule?
       We will have one, right?
       Otherwise what's the point of type-level lambdas?

   NS: We only have sub_cmp in TypingSub (above) now. 
       We need to write down the 'valid' predicate, written 
       (G |= phi) in the .txt. 
       The last two rules in that relation include the reduction 
       relation on types and terms for definition equality.
       That's where the lambdas come in. 
*)

and kinding : env -> typ -> knd -> Type =
  | KindingVar   : g:env
                -> a:var{binds_a g a}
                -> kinding g (TVar a) (lookup_a g a)

  | KindingConst : g:env
                -> t:int{binds_t t}
                -> kinding g (TConst t) (lookup_t t)

  | KindingArr   : g:env
                -> t:typ
                -> c:cmp
                -> kinding g t KType
                -> c_ok (extend g (B_x t)) c
                -> kinding g (TArr t c) KType

  | KindingTTApp : g:env
                 -> t1:typ
                 -> t2:typ
                 -> k:knd{is_KKArr k}
                 -> kinding g t1 k
                 -> kinding g t2 (KKArr.k1 k)
                 -> kinding g (TTApp t1 t2) (subst_knd (TForA t2 0) (KKArr.k2 k))

  | KindingTEApp : g:env
                 -> t1:typ
                 -> e:exp
                 -> k:knd{is_KTArr k}
                 -> kinding g t1 k
                 -> typing g e (tot (KTArr.t k))
                 -> kinding g (TEApp t1 e) (subst_knd (EForX e 0) (KTArr.k k))

  | KindingTTLam : g:env
                -> k:knd
                -> t:typ
                -> k':knd
                -> kind_ok g k
                -> kinding (extend g (B_a k)) t k'
                -> kinding g (TTLam k t) (KKArr k k')

  | KindingTLam :  g:env
                -> t1:typ
                -> t2:typ
                -> k:knd
                -> kinding g t1 KType
                -> kinding (extend g (B_x t1)) t2 k
                -> kinding g (TELam t1 t2) (KTArr t1 k)

and c_ok : env -> cmp -> Type =
  | CPureOK :   g:env
            ->  t:typ
            -> wp:typ
            -> kinding g t KType
            -> kinding g wp (k_pure t)
            -> c_ok g (CPure t wp)

  | CStOK :     g:env
            ->  t:typ
            -> wp:typ
            -> kinding g t KType
            -> kinding g wp (k_st t)
            -> c_ok g (CSt t wp)

and kind_ok : env -> knd -> Type =
  | KOKType : g:env
           -> kind_ok g KType

  | KOKTArr : g:env
           -> t:typ
           -> k:knd
           -> kinding g t KType
           -> kind_ok (extend g (B_x t)) k
           -> kind_ok g (KTArr t k)

  | KOKKArr :  g:env
           -> k1:knd
           -> k2:knd
           -> kind_ok g k1
           -> kind_ok (extend g (B_a k1)) k2
           -> kind_ok g (KKArr k1 k2)

type cfg =
  | Cfg : h:heap -> e:exp -> cfg

type eistep : cfg -> cfg -> Type =
  | EisPure : h:heap ->
              #e:exp ->
              #e':exp ->
              epstep e e' ->
              eistep (Cfg h e) (Cfg h e')
  | EisECtx : h:heap ->
              ee:ectx_ehole ->
              #e:exp ->
              #e':exp ->
              epstep e e' ->
              eistep (Cfg h (plug_e_in_e e ee)) (Cfg h (plug_e_in_e e' ee))
  | EisRd : h:heap ->
            l:loc ->
            eistep (Cfg h (EApp e_bang (ELoc l))) (Cfg h (h l))
  | EisWr : h:heap ->
            l:loc ->
            v:value ->
            eistep (Cfg h (EApp (EApp e_assign (ELoc l)) v))
                   (Cfg (upd_heap l v h) e_unit)


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
(*                                     (\* TODO: + a shift down actually *\) *)
(*                                     (\* for all the betas and twice for fix) *\) *)
(*   | TsTApp_1:  *)

