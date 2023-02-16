module Refl.Typing
open FStar.List.Tot
open FStar.Reflection

module R = FStar.Reflection
module T = FStar.Tactics
module FTB = FStar.Tactics.Builtins
module RTB = Refl.Typing.Builtins

let inspect_pack t = R.inspect_pack_inv t
  
let pack_inspect t = R.pack_inspect_inv t
  
let inspect_pack_bv t = admit ()
  
let pack_inspect_bv t = admit ()

let inspect_pack_binder (bv:_) = admit ()
  
let pack_inspect_binder (t:R.binder) = admit ()
  
let pack_inspect_comp (t:R.comp) = admit ()
  
let inspect_pack_comp (t:R.comp_view) = admit ()

let pack_inspect_fv (fv:R.fv) = admit ()

let inspect_pack_fv (nm:R.name) = admit ()

let pack_inspect_universe u = admit ()

let inspect_pack_universe u = admit ()

let lookup_bvar (e:env) (x:int) : option term = magic ()

let lookup_fvar_uinst (e:R.env) (x:R.fv) (us:list R.universe)
  : option R.term = magic ()

let lookup_bvar_extend_env (g:env) (x y:var) (ty:term) = admit ()

let lookup_fvar_extend_env (g:env) (x:fv) (us:universes) (y:var) (ty:term) = admit ()

let open_or_close_ctx_uvar_and_subst (c:ctx_uvar_and_subst) (v:open_or_close) (i:nat) = magic ()

let open_with (t:term) (v:term) = RTB.open_with t v
  
let open_with_spec (t v:term) = admit ()

let open_term (t:term) (v:var) = RTB.open_term t v

let open_term_spec (t:term) (v:var) = admit ()
  
let close_term (t:term) (v:var) = RTB.close_term t v

let close_term_spec (t:term) (v:var) = admit ()

let rename (t:term) (x y:var)= RTB.rename t x y

let rename_spec (t:term) (x y:var) = admit ()
  
let bv_index_of_make_bv (n:nat) (t:term) = ()

let subtyping_token_renaming (g:env)
                             (bs0:bindings)
                             (bs1:bindings)
                             (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                             (y:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) y) })
                             (t:term)
                             (t0 t1:term)
                             (d:FTB.subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1) = magic ()

let subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term)
                             (d:FTB.subtyping_token (extend_env_l g (bs1@bs0)) t0 t1) = magic ()

let well_typed_terms_are_ln (g:R.env) (e:R.term) (t:R.term) (_:typing g e t) = admit ()

let type_correctness (g:R.env) (e:R.term) (t:R.term) (_:typing g e t) = magic ()
