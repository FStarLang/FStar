(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
  --*)
module Bug237

(* Can only reproduce one of the problems with k_foralle.
   The others only appear in tinyfstar-new.fst *)

open FStar.Classical

type var = nat

type tconst =
  | TcForallE

type typ =
  | TVar   : a:var -> typ
  | TConst : c:tconst -> typ
  | TTApp  : t1:typ -> t2:typ -> typ

type knd =
  | KType : knd
  | KKArr : karg:knd -> kres:knd -> knd
  | KTArr : targ:typ -> kres:knd -> knd

type tsub = var -> Tot typ
opaque type trenaming (s:tsub) = (forall (x:var). is_TVar (s x))

val is_trenaming : s:tsub -> GTot (n:int{(  trenaming s  ==> n=0) /\
                                         (~(trenaming s) ==> n=1)})
let is_trenaming s = (if excluded_middle (trenaming s) then 0 else 1)

val tsub_inc_above : nat -> var -> Tot typ
let tsub_inc_above x y = if y<x then TVar y else TVar (y+1)

val tsub_id :tsub
let tsub_id = fun x -> TVar x

val tsub_inc : var -> Tot typ
let tsub_inc = tsub_inc_above 0

let is_tvar (t:typ) : int = if is_TVar t then 0 else 1

(* Can't reproduce it with this
val ttsubst : s:tsub -> t:typ -> Pure typ (requires True)
      (ensures (fun t' -> trenaming s /\ is_TVar t ==> is_TVar t'))
      (decreases %[is_tvar t; is_trenaming s; t])
val ktsubst : s:tsub -> k:knd -> Tot knd
      (decreases %[1; is_trenaming s; k])

let rec ttsubst s t =
  match t with
  | TVar a -> s a
  | TConst c -> TConst c
  | TTApp t1 t2 -> TTApp (ttsubst s t1) (ttsubst s t2)

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
 *)

(* Can't reproduce it with this either *)
assume type esub
assume val esub_id : esub 
assume val esub_inc : esub

type sub = 
| Sub : es:esub -> ts:tsub -> sub

assume val esub_tlam: s:sub -> Tot esub
assume val esub_elam: s:sub -> Tot esub

opaque type renaming (s:sub) = (trenaming (Sub.ts s))

val is_renaming : s:sub -> GTot (n:int{(  renaming s  ==> n=0) /\
                                       (~(renaming s) ==> n=1)})
let is_renaming s = (if excluded_middle (renaming s) then 0 else 1)

val tsubst : s:sub -> t:typ -> Pure typ (requires True)
      (ensures (fun t' -> renaming s /\ is_TVar t ==> is_TVar t'))
      (decreases %[is_tvar t; is_renaming s;1; t])
val ksubst : s:sub -> k:knd -> Tot knd
      (decreases %[1; is_renaming s; 1; k])
val tsub_elam : s:sub -> a:var -> Tot(t:typ{renaming s ==> is_TVar t}) 
      (decreases %[1; is_renaming s; 0; TVar 0])
val tsub_tlam : s:sub -> a:var -> Tot(t:typ{renaming s ==> is_TVar t}) 
      (decreases %[1; is_renaming s; 0; TVar 0])
val tsub_elam2 : s:sub -> a:var -> Tot(t:typ{renaming s ==> is_TVar t}) 
      (decreases %[1; is_renaming s; 0; TVar 0])

let rec tsub_elam s =
fun a -> tsubst (Sub esub_inc tsub_id) (Sub.ts s a) 

and tsub_tlam s =
fun a -> if a = 0 then TVar a
         else tsubst (Sub esub_id tsub_inc) (Sub.ts s a)

and tsub_elam2 s =
fun a -> tsubst (Sub esub_inc tsub_id) (tsubst (Sub esub_inc tsub_id) (Sub.ts s a))

(*Substitution inside types*)
and tsubst s t =
  match t with
  | TVar a -> (Sub.ts s a)
  | TConst c -> TConst c
  | TTApp t1 t2 -> TTApp (tsubst s t1) (tsubst s t2)

(*Substitution inside kinds*)
and ksubst s k =
  match k with
  | KType -> KType
  | KKArr k kbody -> 
     let sub_tlam = Sub (esub_tlam s) (tsub_tlam s) in
     KKArr (ksubst s k) (ksubst sub_tlam kbody)
  | KTArr t kbody -> 
     let sub_elam = Sub (esub_elam s) (tsub_elam s) in
     (KTArr (tsubst s t) (ksubst sub_elam kbody))

val ktsubst : s:tsub -> k:knd -> Tot knd
let ktsubst s k = ksubst (Sub esub_id s) k

val tsub_beta_gen : var -> typ -> Tot tsub
let tsub_beta_gen x t = fun y -> if y < x then (TVar y)
                                 else if y = x then t
                                 else (TVar (y-1))

val ktsubst_beta_gen : var -> typ -> knd -> Tot knd
let ktsubst_beta_gen x t' = ktsubst (tsub_beta_gen x t')

let ktsubst_beta = ktsubst_beta_gen 0

type eenv = var -> Tot (option typ)
type tenv = var -> Tot (option knd)

type env =
| Env : e:eenv -> t:tenv -> env

val tconsts : tconst -> Tot knd
let tconsts tc =
  match tc with
  | TcForallE   -> KKArr KType (KKArr (KTArr (TVar 0) KType) KType)

type kinding : g:env -> t:typ -> k:knd -> Type =
| KConst : g:env -> c:tconst ->
    kinding g (TConst c) (tconsts c)

| KTApp : #g:env -> #t1:typ -> #t2:typ -> #k:knd -> #k':knd ->
          =hk1:kinding g t1 (KKArr k k') ->
          =hk2:kinding g t2 k ->
               (* kinding g (TTApp t1 t2) k' *)
               kinding g (TTApp t1 t2) (ktsubst_beta t2 k')

val k_foralle : #g:env -> #t1:typ -> #t2:typ ->
                =hk1:kinding g t1 KType ->
                Tot (kinding g (TTApp (TConst TcForallE) t1)
                               (KKArr (KTArr t1 KType) KType))
let k_foralle g t1 t2 hk1 =
  (* assert(KKArr (KTArr t1 KType) KType =  *)
  (*        ktsubst_beta t1 (KKArr (KTArr (TVar 0) KType) KType)); *)
  KTApp (*KKArr (KTArr (TVar 0) KType) KType*) (KConst g TcForallE) hk1
(* Problem: without the annotation and the explicit k' in KTApp
   this causes "Unresolved implicit argument" *)
