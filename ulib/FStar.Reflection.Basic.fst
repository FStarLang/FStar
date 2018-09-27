module FStar.Reflection.Basic

open FStar.Order
open FStar.Reflection.Types
open FStar.Reflection.Data

(* Views  *)
assume val inspect_ln     : (t:term) -> tv:term_view{smaller tv t}
assume val pack_ln        : term_view -> term

assume val inspect_comp   : (c:comp) -> cv:comp_view{smaller_comp cv c}
assume val pack_comp      : comp_view -> comp

assume val inspect_sigelt : sigelt -> sigelt_view
assume val pack_sigelt    : sigelt_view -> sigelt

assume val inspect_fv     : fv -> name
assume val pack_fv        : name -> fv

assume val inspect_bv     : bv -> bv_view
assume val pack_bv        : bv_view -> bv

assume val inspect_binder : binder -> bv * aqualv
assume val pack_binder    : bv -> aqualv -> binder

(* Primitives & helpers *)
assume val lookup_typ     : env -> name -> option sigelt
assume val compare_bv     : bv -> bv -> order
assume val binders_of_env : env -> binders
assume val moduleof       : env -> list string
assume val is_free        : bv -> term -> bool
assume val lookup_attr    : term -> env -> list fv
assume val term_eq        : term -> term -> bool
assume val term_to_string : term -> string

(* Attributes are terms, not to be confused with Prims.attribute *)
assume val sigelt_attrs     : sigelt -> list term
assume val set_sigelt_attrs : list term -> sigelt -> sigelt
