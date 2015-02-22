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
type var = int    //de Bruijn index
type const = int  // CH: trying to pack all exp and typ constants
                  // and locations in one int seems very unelegant
                  // (and will need quite a complex encoding, since
                  //  constants include integers and locations are
                  //  also an infinite set)
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
  | CST   : t:typ -> wp:typ -> cmp

and exp =
  | EVar   : x:var   -> exp
  | EConst : c:const -> exp
  | ELoc   : l:int   -> exp
  | ENat   : l:int   -> exp (* CH: weren't ints just constants? *)
  | ELam   : t:typ   -> e:exp -> exp            (* x:t bound in e *)
  | EApp   : e1:exp  -> e2:exp -> exp
  | ELet   : t:typ   -> e1:exp -> e2:exp -> exp (* x:t bound in e2 *)
  (* CH: if I remember correctly let was to simulate the other contexts?
     Is this part of the language or not? I don't see why we would need it.
     It also doesn't appear in the txt. *)
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

let e_bang   = EConst 100
let e_assign = EConst 101
let e_sel    = EConst 102
let e_upd    = EConst 103
let e_unit   = EConst 104
(* CH: still missing the integer constants *)

(********************************************************)
(* Substitutions and de Bruijn index manipulations      *)
(********************************************************)

(* TODO: finish this up
   CH: try to reuse parallel substitution style from lambda_omega *)

type subst =
  | EForX : e:exp -> x:var -> subst
  | TForA : t:typ -> a:var -> subst

assume val bump_knd' : int -> int -> k:knd -> Tot knd (decreases k)
assume val bump_cmp': int -> int -> c:cmp -> Tot cmp (decreases c)
assume val bump_exp' : int -> int -> e:exp -> Tot exp (decreases e)

val bump_typ' : m:int -> n:int -> t:typ -> Tot typ (decreases t)
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
(* The signatures of Pure and ST and other Monad ops    *)
(********************************************************)
let k_pre_pure    = KType
let k_post_pure t = KTArr t KType
let k_pure t      = KKArr (k_post_pure t) k_pre_pure

let k_pre_st      = KTArr t_heap KType
let k_post_st t   = KTArr t (KTArr t_heap KType)
let k_st t        = KKArr (k_post_st t) k_pre_st

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
              (TTApp (bump_typ 1 wp1)
                 (TELam (* x *)
                    (bump_typ 1 t1)
                    (TTApp
                       (TEApp (bump_typ 2 wp2) (EVar 0))
                       (TVar 1)))))


val lift_pure_st : c1:cmp{is_CPure c1}
                -> Tot cmp
let lift_pure_st (CPure t wp) =
  CST t (TTLam (* post *)
           (k_post_st t)
           (TELam (* h *)
              t_heap
              (TTApp (bump_typ 2 wp)
                 (TELam (* x *)
                    t
                    (TEApp (TEApp (TVar 2) (*post*) (EVar 0) (*x*)) (EVar 1)(*h*))))))

val bind_st:  c1:cmp{is_CST c1}
           -> c2:cmp{is_CST c2}
           -> Tot cmp
let bind_st (CST t1 wp1) (CST t2 wp2) =
  let wp2 = TELam t1 wp2 in
  CST t2 (TTLam (* post *)
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
  | CST _ _,   CST _ _   -> bind_st   c1 c2
  | CST _ _,   CPure _ _ -> bind_st   c1 (lift_pure_st c2)
  | CPure _ _, CST _ _   -> bind_st   (lift_pure_st c1) c2

let conj phi1 phi2        = TTApp (TTApp t_and phi1) phi2
let close_forall t phi    = TTApp (TTApp t_forall t) (TELam t phi)

let down_CPure t wp       = TTApp (TTApp t_forall_post_pure t)
                                  (TTLam (k_post_pure t) (TTApp (bump_typ 1 wp) (TVar 0)))
let down_CST t wp         = TTApp (TTApp t_forall_post_st t)
                                  (TTLam (k_post_st t)
                                     (TELam t_heap (TEApp (TTApp (bump_typ 2 wp) (TVar 1)) (EVar 0))))
let up_CPure t phi        = TTLam (k_post_pure t) (bump_typ 1 phi)
let up_CST   t phi        = TTLam (k_post_st t)   (TELam t_heap (bump_typ 2 phi))
let op_CPure t op wp1 wp2 = TTLam (k_post_pure t) (TTApp (TTApp op
                                                            (TTApp (bump_typ 1 wp1) (TVar 0)))
                                                           (TTApp (bump_typ 1 wp2) (TVar 0)))
let op_CST t op wp1 wp2   = TTLam (k_post_st t)   (TELam t_heap (TTApp (TTApp op
                                                                         (TEApp (TTApp (bump_typ 2 wp1) (TVar 1)) (EVar 0)))
                                                                  (TEApp (TTApp (bump_typ 2 wp2) (TVar 1)) (EVar 0))))

let mk_eq t e1 e2      = TEApp (TEApp (TTApp t_eq t) e1) e2
let neg phi            = TTApp t_neg phi

val bind_pure_if : exp -> c1:cmp{is_CPure c1} -> c2:cmp{is_CPure c2} -> Tot cmp
let bind_pure_if e (CPure t wp1) (CPure _ wp2) =
  let guard = mk_eq t_int e (ENat 0) in
  let wp = op_CPure t t_and (op_CPure t t_imp (up_CPure t guard) wp1) (op_CPure t t_imp (up_CPure t (neg guard)) wp2) in
  CPure t wp

val bind_st_if : exp -> c1:cmp{is_CST c1} -> c2:cmp{is_CST c2} -> Tot cmp
let bind_st_if e (CST t wp1) (CST _ wp2) =
  let guard = mk_eq t_int e (ENat 0) in
  let wp = op_CST t t_and (op_CST t t_imp (up_CST t guard) wp1) (op_CST t t_imp (up_CST t (neg guard)) wp2) in
  CST t wp

val bind_if : exp -> cmp -> cmp -> Tot cmp
let bind_if e c1 c2 = match c1, c2 with
  | CPure _ _, CPure _ _ -> bind_pure_if e c1 c2
  | CPure _ _, CST _ _   -> bind_st_if e (lift_pure_st c1) c2
  | CST _ _, CPure _ _   -> bind_st_if e c1 (lift_pure_st c2)
  | CST _ _, CST _ _     -> bind_st_if e c1 c2

let result_typ = function
  | CPure t _
  | CST t  _   -> t

let set_result_typ c t = match c with
  | CPure _ wp ->  CPure t wp
  | CST _ wp -> CST t wp

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
                                        aren't they dynamically allocated?
                                        (in the txt they are in environment)
                                        (they anyway all have type ref int) *)
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
       in a low-level deduction system *)
assume type valid: env -> typ -> Type

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
           -> sub_cmp g (CST t wp1) (CST t wp2)
                      (down_CST t (op_CST t t_imp wp2 wp1))

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

type typing : env -> exp -> cmp -> Type =
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

(* CH: Missing the 2 fix rules (see T-Fix and T-FixOmega in txt) *)
(* CH: Where is the type conversion (typing or subtyping) rule?
       We will have one, right?
       Otherwise what's the point of type-level lambdas? *)

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

  | CSTOK :     g:env
            ->  t:typ
            -> wp:typ
            -> kinding g t KType
            -> kinding g wp (k_st t)
            -> c_ok g (CST t wp)

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

(* CH: still missing the operational semantics (see txt);
   it needs to be a relation because of allocation,
   and of full reduction in types, right? *)

(* Values *)

val is_value : exp -> Tot bool
let is_value e =
  match e with
  | EVar _
  | EConst _
  | ELoc _
  | ENat _
  | ELam _ _
  | EFix _ _ _ -> true
  | EApp _ _
  | ELet _ _ _
  | EIf0 _ _ _ -> false

type value = e:exp{is_value e}

(* Contexts *)

type ectx_ehole =
  | EETop : ectx_ehole
  | EEAppL : e2:exp -> ectx_ehole
  | EEAppR : e1:value -> ectx_ehole
  | EEIf0 : e1:exp -> e2:exp -> ectx_ehole

type ectx_thole =
  | ETLam : e:exp -> ectx_thole
  | ETFix : ed:(option exp) -> e:exp -> ectx_thole

type cctx =
  | CCPureT : wp:typ -> cctx
  | CCPureWP : t:typ -> cctx

type tctx_thole =
  | TTTop : tctx_thole
  | TTArrT : c:cmp -> tctx_thole
  | TTArrC : t:typ -> c:cctx -> tctx_thole
  | TTTAppL : t2:typ -> tctx_thole
  | TTTAppR : t1:typ -> tctx_thole
  | TTEApp : e:exp -> tctx_thole
  | TTTLam : k:knd -> tctx_thole
  | TTELam1 : t2:typ -> tctx_thole
  | TTELam2 : t1:typ -> tctx_thole

type tctx_ehole =
  | TETEApp : t:typ -> tctx_ehole

