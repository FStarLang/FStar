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

type var = int
type const = int
type knd = 
  | KType : knd
  | KTArr : x:var -> t:typ -> k:knd -> knd
  | KKArr : a:var -> k1:knd -> k2:knd -> knd

and typ = 
  | TVar   : a:var   -> typ
  | TConst : c:const -> typ
  | TArr   : x:var   -> t:typ  -> c:comp -> typ
  | TTApp  : t1:typ  -> t2:typ -> typ
  | TEApp  : t:typ   -> e:exp  -> typ
  | TTLam  : a:var   -> k:knd  -> t:typ  -> typ
  | TLam   : x:var   -> t1:typ -> t2:typ -> typ

and comp = 
  | CPure : t:typ -> wp:typ -> comp
  | CST   : t:typ -> wp:typ -> comp

and exp = 
  | ELoc   : l:int   -> exp
  | ENat   : l:int   -> exp
  | EVar   : x:var   -> exp
  | EConst : c:const -> exp
  | ELam   : x:var   ->  t:typ ->  e:exp -> exp
  | EApp   : e1:exp  -> e2:exp -> exp
  | ELet   : x:var   ->  t:typ -> e1:exp -> e2:exp -> exp
  | EIf0   : e0:exp  -> e1:exp -> e2:exp -> exp

      
let t_unit   = TConst 0
let t_nat    = TConst 1
let t_refint = TConst 2
let t_heap   = TConst 3
let t_forall = TConst 4
let t_and    = TConst 5
let t_imp    = TConst 6
let t_neg    = TConst 7
let t_eq     = TConst 8

let e_bang   = EConst 0
let e_assign = EConst 1
let e_sel    = EConst 2
let e_upd    = EConst 3

let var_a    = 0
let var_b    = 1
let var_post = 2
let t_post   = TVar var_post

let var_x    = 3
let e_x      = EVar var_x

let var_y    = 4
let var_h    = 5

let k_pre_pure    = KType
let k_post_pure t = KTArr var_x t KType
let k_pure t      = KKArr var_post (k_post_pure t) k_pre_pure

let k_pre_st      = KTArr var_h t_heap KType
let k_post_st t   = KTArr var_x t (KTArr var_h t_heap KType)
let k_st t        = KKArr var_post (k_post_st t) k_pre_st

let tot t = CPure t (TTLam var_post (k_post_pure t) 
                      (TTApp (TTApp t_forall t)
                             (TLam var_x t (TEApp t_post e_x))))

type binding =
  | TBinding  : k:knd -> binding
  | VBinding  : t:typ -> binding
  | LBinding  : t:typ -> binding
  | CBinding  : t:typ -> binding
  | TCBinding : k:knd -> binding

type env = var -> Tot (option binding)

val extend: env -> int -> binding -> Tot env
let extend g a b = fun x -> if x = a then Some b else g a

val binds: test:(binding -> Tot bool) -> env -> var -> Tot bool
let binds test g x = match g x with 
  | Some b -> test b
  | _ -> false

let binds_tvar   = binds is_TBinding
let binds_var    = binds is_VBinding
let binds_loc    = binds is_LBinding
let binds_const  = binds is_CBinding
let binds_tconst = binds is_TCBinding

val lookup: a:Type
         -> test:(binding -> Tot bool) 
         -> g:env 
         -> x:var{binds test g x}
         -> project:(b:binding{test b} -> Tot a)
         -> Tot a
let lookup test g x project = let Some b = g x in project b

let lookup_knd    g x = lookup is_TBinding  g x TBinding.k
let lookup_typ    g x = lookup is_VBinding  g x VBinding.t
let lookup_loc    g x = lookup is_LBinding  g x LBinding.t
let lookup_const  g x = lookup is_CBinding  g x CBinding.t
let lookup_tconst g x = lookup is_TCBinding g x TCBinding.k

type subst = 
  | EForX : e:exp -> x:var -> subst
  | TForA : t:typ -> a:var -> subst

assume val subst_comp: subst -> comp -> Tot comp
assume val subst_typ:  subst -> typ -> Tot typ
assume val subst_knd:  subst -> knd -> Tot knd

val bind_pure:  c1:comp{is_CPure c1} 
             -> x:var 
             -> c2:comp{is_CPure c2}
             -> Tot comp
let bind_pure (CPure t1 wp1) x (CPure t2 wp2) = 
  CPure t2 (TTLam var_post (k_post_pure t2) (TTApp wp1 (TLam x t1 (TTApp wp2 t_post))))


val lift_pure_st : c1:comp{is_CPure c1}
                -> Tot comp  
let lift_pure_st (CPure t wp) = 
  CST t (TTLam var_post (k_post_st t)
           (TLam var_h t_heap (TTApp wp (TLam var_x t (TEApp (TEApp t_post (EVar var_x)) (EVar var_h))))))
  
val bind_st:  c1:comp{is_CST c1} 
           -> x:var 
           -> c2:comp{is_CST c2}
           -> Tot comp
let bind_st (CST t1 wp1) x (CST t2 wp2) = 
  CST t2 (TTLam var_post (k_post_st t2) (TTApp wp1 (TLam x t1 (TTApp wp2 t_post))))

val bind: c1:comp -> x:var -> c2:comp -> Tot comp 
let bind c1 x c2 = match c1, c2 with 
  | CPure _ _, CPure _ _ -> bind_pure c1 x c2
  | CST _ _, CST _ _     -> bind_st c1 x c2
  | CST _ _, CPure _ _   -> bind_st c1 x (lift_pure_st c2)
  | CPure _ _, CST _ _   -> bind_st (lift_pure_st c1) x c2


let up_CPure t phi      = TTLam var_post (k_post_pure t) phi
let up_CST t phi        = TTLam var_post (k_post_st t) (TLam var_h t_heap phi)
let op_CPure t op wp1 wp2 = TTLam var_post (k_post_pure t) (TTApp (TTApp op 
                                                                 (TTApp wp1 t_post)) 
                                                           (TTApp wp2 t_post))
let op_CST t op wp1 wp2   = TTLam var_post (k_post_st t) (TLam var_h t_heap (TTApp (TTApp op 
                                                                                     (TEApp (TTApp wp1 t_post) (EVar var_h)))
                                                                               (TEApp (TTApp wp2 t_post) (EVar var_h))))
let mk_eq t e1 e2      = TEApp (TEApp (TTApp t_eq t) e1) e2
let neg phi            = TTApp t_neg phi

val bind_pure_if : exp -> c1:comp{is_CPure c1} -> c2:comp{is_CPure c2} -> Tot comp  
let bind_pure_if e (CPure t wp1) (CPure _ wp2) =
  let guard = mk_eq t_nat e (ENat 0) in
  let wp = op_CPure t t_and (op_CPure t t_imp (up_CPure t guard) wp1) (op_CPure t t_imp (up_CPure t (neg guard)) wp2) in
  CPure t wp
    
val bind_st_if : exp -> c1:comp{is_CST c1} -> c2:comp{is_CST c2} -> Tot comp  
let bind_st_if e (CST t wp1) (CST _ wp2) =
  let guard = mk_eq t_nat e (ENat 0) in
  let wp = op_CST t t_and (op_CST t t_imp (up_CST t guard) wp1) (op_CST t t_imp (up_CST t (neg guard)) wp2) in
  CST t wp

val bind_if : exp -> comp -> comp -> Tot comp
let bind_if e c1 c2 = match c1, c2 with 
  | CPure _ _, CPure _ _ -> bind_pure_if e c1 c2
  | CPure _ _, CST _ _   -> bind_st_if e (lift_pure_st c1) c2
  | CST _ _, CPure _ _   -> bind_st_if e c1 (lift_pure_st c2)
  | CST _ _, CST _ _     -> bind_st_if e c1 c2

let result_typ = function 
  | CPure t _ 
  | CST t  _   -> t

type typing : env -> exp -> comp -> Type = 
  | TypingLoc   : g:env 
               -> l:int{binds_loc g l /\ lookup_loc g l = t_refint}   
               -> typing g (ELoc l) (tot t_refint)

  | TypingVar   : g:env 
               -> x:var{binds_var g x}   
               -> kinding g (lookup_typ g x) KType
               -> typing g (EVar x) (tot (lookup_typ g x))

  | TypingConst : g:env 
               -> c:int{binds_const g c} 
               -> kinding g (lookup_const g c) KType
               -> typing g (EConst c) (tot (lookup_const g c))

  | TypingAbs  : g:env 
              -> x:var
              -> t:typ
              -> e:exp
              -> kinding g t KType
              -> c:comp
              -> typing (extend g x (VBinding t)) e c
              -> typing g (ELam x t e) (tot (TArr x t c))

  | TypingApp :  g:env 
             -> e1:exp
             -> e2:exp
             -> tarr:typ{is_TArr tarr}
             -> typing g e1 (tot tarr)
             -> typing g e2 (tot (TArr.t tarr))
             -> typing g (EApp e1 e2) (subst_comp (EForX e2 (TArr.x tarr)) (TArr.c tarr))

  | TypingLet : g:env 
             -> x:var 
             -> e1:exp
             -> e2:exp
             -> c1:comp
             -> c2:comp 
             -> typing g e1 c1
             -> typing (extend g x (VBinding (result_typ c1))) e2 c2
             -> typing g (ELet x (result_typ c1) e1 e2) (bind c1 x c2)

  | TypingIf : g:env 
            -> e0:exp
            -> e1:exp 
            -> e2:exp
            -> c1:comp
            -> c2:comp{result_typ c1 = result_typ c2}
            -> typing g e0 (tot t_nat)
            -> typing g e1 c1
            -> typing g e2 c2
            -> typing g (EIf0 e0 e1 e2) (bind_if e0 c1 c2)

and kinding : env -> typ -> knd -> Type = 
  | KindingVar   : g:env -> a:var{binds_tvar g a} -> kinding g (TVar a) (lookup_knd g a)

  | KindingConst : g:env -> tc:int{binds_tconst g tc} -> kinding g (TConst tc) (lookup_tconst g tc)

  | KindingArr   : g:env -> x:var -> t:typ -> c:comp 
                -> kinding g t KType
                -> c_ok (extend g x (VBinding t)) c
                -> kinding g (TArr x t c) KType

  | KindingTTApp : g:env -> t1:typ -> t2:typ -> k:knd{is_KKArr k}
                 -> kinding g t1 k
                 -> kinding g t2 (KKArr.k1 k)
                 -> kinding g (TTApp t1 t2) (subst_knd (TForA t2 (KKArr.a k)) (KKArr.k2 k))

  | KindingTEApp : g:env -> t1:typ -> e:exp -> k:knd{is_KTArr k}
                 -> kinding g t1 k
                 -> typing g e (tot (KTArr.t k))
                 -> kinding g (TEApp t1 e) (subst_knd (EForX e (KTArr.x k)) (KTArr.k k))

  | KindingTTLam : g:env -> a:var -> k:knd -> t:typ -> k':knd
                -> kind_ok g k 
                -> kinding (extend g a (TBinding k)) t k'
                -> kinding g (TTLam a k t) (KKArr a k k')

  | KindingTLam :  g:env -> x:var -> t1:typ -> t2:typ -> k:knd
                -> kinding g t1 KType
                -> kinding (extend g x (VBinding t1)) t2 k
                -> kinding g (TLam x t1 t2) (KTArr x t1 k)

and c_ok : env -> comp -> Type = 
  | CPureOK : g:env -> t:typ -> wp:typ 
            -> kinding g t KType
            -> kinding g wp (k_pure t)
            -> c_ok g (CPure t wp)

  | CSTOK : g:env -> t:typ -> wp:typ 
            -> kinding g t KType
            -> kinding g wp (k_st t)
            -> c_ok g (CST t wp)

and kind_ok : env -> knd -> Type = 
  | KOKType : g:env -> kind_ok g KType

  | KOKTArr : g:env -> x:var -> t:typ -> k:knd 
           -> kinding g t KType
           -> kind_ok (extend g x (VBinding t)) k
           -> kind_ok g (KTArr x t k)

  | KOKKArr : g:env -> a:var -> k1:knd -> k2:knd 
           -> kind_ok g k1
           -> kind_ok (extend g a (TBinding k1)) k2
           -> kind_ok g (KKArr a k1 k2)
          
         
     
    
      

                                 
                             
