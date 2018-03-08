module FStar.Reflection.Basic

open FStar.Order
open FStar.Tactics.Effect
open FStar.Reflection.Types
open FStar.Reflection.Data

(* The main characters *)
assume private val __type_of_binder: binder -> term
let type_of_binder (b:binder) : Tac term = __type_of_binder b

assume private val __inspect : term -> term_view
let inspect t : Tac term_view = __inspect t

assume private val __pack : term_view -> term
let pack tv : Tac term = __pack tv

assume private val __inspect_comp : comp -> comp_view
let inspect_comp (c:comp) : Tac comp_view = __inspect_comp c

assume private val __pack_comp : comp_view -> comp
let pack_comp (cv:comp_view) : Tac comp = __pack_comp cv

assume private val __inspect_sigelt : sigelt -> sigelt_view
let inspect_sigelt (se:sigelt) : Tac sigelt_view = __inspect_sigelt se

assume private val __pack_sigelt : sigelt_view -> sigelt
let pack_sigelt (sv:sigelt_view) : Tac sigelt = __pack_sigelt sv

assume private val __inspect_fv : fv -> name
let inspect_fv (fv:fv) : Tac name = __inspect_fv fv

assume private val __pack_fv : name -> fv
let pack_fv (ns:name) : Tac fv = __pack_fv ns

assume private val __lookup_typ : env -> name -> option sigelt
let lookup_typ (e:env) (ns:name) : Tac (option sigelt) = __lookup_typ e ns

assume private val __compare_binder : binder -> binder -> order
let compare_binder (b1:binder) (b2:binder) : Tac order = __compare_binder b1 b2

assume private val __inspect_bv : binder -> string
let inspect_bv (b:binder) : Tac string = __inspect_bv b

assume private val __binders_of_env : env -> binders
let binders_of_env (e:env) : Tac binders = __binders_of_env e

assume private val __is_free : binder -> term -> bool
let is_free (b:binder) (t:term) : Tac bool = __is_free b t

assume private val __term_eq : term -> term -> bool
let term_eq t1 t2 : Tac bool = __term_eq t1 t2

assume private val __term_to_string : term -> string
let term_to_string t : Tac string = __term_to_string t
