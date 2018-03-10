module FStar.Reflection.Basic

open FStar.Order
open FStar.Reflection.Types
open FStar.Reflection.Data

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

assume private val __inspect_sigelt : sigelt -> sigelt_view
let inspect_sigelt (se:sigelt) : sigelt_view = __inspect_sigelt se

assume private val __pack_sigelt : sigelt_view -> sigelt
let pack_sigelt (sv:sigelt_view) : sigelt = __pack_sigelt sv

assume private val __inspect_fv : fv -> name
let inspect_fv (fv:fv) : name = __inspect_fv fv

assume val __pack_fv : name -> fv
let pack_fv (ns:name) = __pack_fv ns

assume val __inspect_bv : bv -> bv_view
let inspect_bv (bv:bv) : bv_view = __inspect_bv bv

assume val __pack_bv : bv_view -> bv
let pack_bv (bvv:bv_view) : bv = __pack_bv bvv

assume val __inspect_binder : binder -> bv * aqualv
let inspect_binder b = __inspect_binder b

assume val __pack_binder : bv -> aqualv -> binder
let pack_binder bv aq = __pack_binder bv aq

assume private val __lookup_typ : env -> name -> option sigelt
let lookup_typ (e:env) (ns:name) : option sigelt = __lookup_typ e ns

assume val __compare_bv : bv -> bv -> order
let compare_bv (b1:bv) (b2:bv) = __compare_bv b1 b2

assume private val __binders_of_env : env -> binders
let binders_of_env (e:env) : binders = __binders_of_env e

assume private val __is_free : bv -> term -> bool
let is_free (bv:bv) (t:term) : bool = __is_free bv t

assume private val __term_eq : term -> term -> bool
let term_eq t1 t2 : bool = __term_eq t1 t2

(* Should be TAC, printing might depend on gensym *)
assume val __term_to_string : term -> string
let term_to_string t : string = __term_to_string t
