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

module Pulse.Elaborate
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
include Pulse.Elaborate.Core
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Elaborate.Pure
open Pulse.Typing

val elab_open_commute' (e:term)
                       (v:term)
                       (n:index)
  : Lemma (ensures
              RT.subst_term e [ RT.DT n v ] ==
              (open_term' e v n))

val elab_close_commute' (e:term)
                        (v:var)
                        (n:index)
  : Lemma (RT.subst_term e [ RT.ND v n ] ==
           (close_term' e v n))

val elab_comp_close_commute (c:comp) (x:var)
  : Lemma (elab_comp (close_comp c x) == RT.close_term (elab_comp c) x)

val elab_comp_open_commute (c:comp) (x:term)
  : Lemma (elab_comp (open_comp_with c x) == RT.open_with (elab_comp c) x)

val elab_ln_comp (c:comp) (i:int)
  : Lemma (requires ln_c' c i) (ensures RT.ln' (elab_comp c) i)
