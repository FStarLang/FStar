module FStar.Meta.Tc.Builtins

open FStar.Reflection
open FStar.Meta.Tc.Effect

open FStar.Reflection.Helpers
open FStar.Reflection.Subst

val valid_prop_token (en:env) (t:typ) : Type0
val subtyping_token (en:env) (t1 t2:typ) : Type0

///
/// Should these return option or raise exceptions?
/// 

val check_prop_validity (en:env) (t:typ) : MetaTcT (valid_prop_token en t)
val check_subtyping (en:env) (t1 t2:typ) : MetaTcT (option (subtyping_token en t1 t2))

val subtyping_token_renaming (g:env)
                             (bs0:bindings)
                             (bs1:bindings)
                             (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                             (y:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) y) })
                             (t:term)
                             (t0 t1:term)
                             (d:subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1)
  : subtyping_token (extend_env_l g (rename_bindings bs1 x y@(y,t)::bs0))
                    (rename t0 x y)
                    (rename t1 x y)

val subtyping_token_weakening (g:env)
                              (bs0:bindings)
                              (bs1:bindings)
                              (x:var { None? (lookup_bvar (extend_env_l g (bs1@bs0)) x) })
                              (t:term)
                              (t0 t1:term)
                             (d:subtyping_token (extend_env_l g (bs1@bs0)) t0 t1)
  : subtyping_token (extend_env_l g (bs1@(x,t)::bs0)) t0 t1
