module FStar.Reflection.Basic

open FStar.Order
open FStar.Reflection.Types
open FStar.Reflection.Data

assume private val __type_of_binder: binder -> term
let type_of_binder (b:binder) : term = __type_of_binder b

let rec forall_list (p:'a -> Type) (l:list 'a) : Type =
    match l with
    | [] -> True
    | x::xs -> p x /\ forall_list p xs

(* Comparison of a term_view to term. Allows to recurse while changing the view *)
val smaller : term_view -> term -> Type0
let smaller tv t =
    match tv with
    | Tv_App l r ->
        l << t /\ r << t

    | Tv_Abs b t'
    | Tv_Arrow b t'
    | Tv_Refine b t' ->
        type_of_binder b << t /\ t' << t

    | Tv_Let b t1 t2 ->
        type_of_binder b << t /\ t1 << t /\ t2 << t

    | Tv_Match t1 brs ->
        t1 << t /\ (forall_list (fun (b, t') -> t' << t) brs)

    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown
    | Tv_Var _
    | Tv_Uvar _ _
    | Tv_FVar _ -> True

val smaller_comp : comp_view -> comp -> Type0
let smaller_comp cv c =
    match cv with
    | C_Total t ->
        t << c
    | C_Lemma pre post ->
        pre << c /\ post << c
    | C_Unknown ->
        True

(* The main characters *)
assume val __inspect : t:term -> tv:term_view{smaller tv t}
let inspect t : term_view = __inspect t

assume val __pack : term_view -> term
let pack tv : term = __pack tv

assume val __inspect_comp : c:comp -> cv:comp_view{smaller_comp cv c}
let inspect_comp (c:comp) = __inspect_comp c

assume val __pack_comp : comp_view -> comp
let pack_comp (cv:comp_view) = __pack_comp cv

(* They are inverses *)
assume val pack_inspect_inv : (t:term) -> Lemma (pack (inspect t) == t)
assume val inspect_pack_inv : (tv:term_view) -> Lemma (inspect (pack tv) == tv)

assume val __inspect_fv : fv -> name
let inspect_fv (fv:fv) = __inspect_fv fv

assume val __pack_fv : name -> fv
let pack_fv (ns:name) = __pack_fv ns

assume val __lookup_typ : env -> name -> sigelt_view
let lookup_typ (e:env) (ns:name) = __lookup_typ e ns

assume val __compare_binder : binder -> binder -> order
let compare_binder (b1:binder) (b2:binder) = __compare_binder b1 b2

assume val __inspect_bv : binder -> string
let inspect_bv (b:binder) = __inspect_bv b

assume private val __binders_of_env : env -> binders
let binders_of_env (e:env) : binders = __binders_of_env e

assume private val __is_free : binder -> term -> bool
let is_free (b:binder) (t:term) : bool = __is_free b t

assume private val __term_eq : term -> term -> bool
let term_eq t1 t2 : bool = __term_eq t1 t2

assume val __term_to_string : term -> string
let term_to_string t : string = __term_to_string t

(* Shouldn't this be TAC??? *)
assume val __fresh_binder : typ -> binder
let fresh_binder t : binder = __fresh_binder t
