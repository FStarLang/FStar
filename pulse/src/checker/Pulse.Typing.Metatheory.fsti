(*
   Copyright 2023 Microsoft Research

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
  : Dv (st_typing (push_env g1 g') t c)

val st_typing_weakening_standard
  (#g:env) (#t:st_term) (#c:comp) (d:st_typing g t c)
  (g1:env { g1 `env_extends` g })
  : Dv (st_typing g1 t c)

val st_typing_weakening_end
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (d:st_typing (push_env g g') t c)
  (g'':env { g'' `env_extends` g' /\ disjoint g'' g })
  : Dv (st_typing (push_env g g'') t c)

val veq_weakening
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:slprop) (d:slprop_equiv (push_env g g') v1 v2)
  (g1:env { g1 `env_extends` g /\ disjoint g1 g' })
  : slprop_equiv (push_env g1 g') v1 v2

val veq_weakening_end
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:slprop) (d:slprop_equiv (push_env g g') v1 v2)
  (g'':env { g'' `env_extends` g' /\ disjoint g'' g })
  : slprop_equiv (push_env g g'') v1 v2
