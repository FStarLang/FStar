module Pulse.Typing.Metatheory
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

include Pulse.Typing.Metatheory.Base

val tot_typing_weakening_single (#g:env) (#t #ty:term)
  (d:tot_typing g t ty)
  (x:var { ~ (x `Set.mem` dom g)})
  (x_t:typ)

  : tot_typing (push_binding g x ppname_default x_t) t ty

val tot_typing_weakening_standard (g:env)
  (#t #ty:term) (d:tot_typing g t ty)
  (g1:env { g1 `env_extends` g })
  : tot_typing g1 t ty

val st_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (d:st_typing (push_env g g') t c)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : st_typing (push_env g1 g') t c

val st_typing_weakening_standard
  (#g:env) (#t:st_term) (#c:comp) (d:st_typing g t c)
  (g1:env { g1 `env_extends` g })
  : st_typing g1 t c

val st_typing_weakening_end
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (d:st_typing (push_env g g') t c)
  (g'':env { g'' `env_extends` g' /\ disjoint g'' g })
  : st_typing (push_env g g'') t c

val veq_weakening
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:vprop) (d:vprop_equiv (push_env g g') v1 v2)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : vprop_equiv (push_env g1 g') v1 v2

val veq_weakening_end
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:vprop) (d:vprop_equiv (push_env g g') v1 v2)
  (g'':env { g'' `env_extends` g' /\ disjoint g'' g })
  : vprop_equiv (push_env g g'') v1 v2
