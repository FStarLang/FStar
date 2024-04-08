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
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate.Core
              
#push-options "--fuel 10 --ifuel 10 --z3rlimit_factor 30 --query_stats --z3cliopt 'smt.qi.eager_threshold=100'"          

let elab_open_commute' (e:term)
                       (v:term)
                       (n:index)
  : Lemma (ensures
              RT.subst_term e [ RT.DT n v ] ==
              (open_term' e v n))
  = ()

let elab_comp_open_commute' (c:comp) (v:term) (n:index)
  : Lemma (ensures
              RT.subst_term (elab_comp c) [ RT.DT n v ] ==
              elab_comp (open_comp' c v n))
  = match c with
    | C_Tot t -> elab_open_commute' t v n
    | C_ST s ->
      elab_open_commute' s.res v n;
      elab_open_commute' s.pre v n;
      elab_open_commute' s.post v (n + 1)
    | C_STGhost inames s
    | C_STAtomic inames _ s ->
      elab_open_commute' inames v n;
      elab_open_commute' s.res v n;
      elab_open_commute' s.pre v n;
      elab_open_commute' s.post v (n + 1)

let elab_close_commute' (e:term)
                        (v:var)
                        (n:index)
  : Lemma (ensures (
              RT.subst_term e [ RT.ND v n ] ==
              (close_term' e v n)))
  = ()

let elab_comp_close_commute' (c:comp) (v:var) (n:index)
  : Lemma (ensures
              RT.subst_term (elab_comp c) [ RT.ND v n ] ==
              elab_comp (close_comp' c v n))
          (decreases c)
  = match c with
    | C_Tot t -> elab_close_commute' t v n
    | C_ST s ->
      elab_close_commute' s.res v n;
      elab_close_commute' s.pre v n;
      elab_close_commute' s.post v (n + 1)
    | C_STGhost inames s 
    | C_STAtomic inames _ s ->
      elab_close_commute' inames v n;
      elab_close_commute' s.res v n;
      elab_close_commute' s.pre v n;
      elab_close_commute' s.post v (n + 1)

let elab_open_commute (t:term) (x:var)
  : Lemma (open_term t x == RT.open_term t x)
  = RT.open_term_spec t x;
    elab_open_commute' t (null_var x) 0

let elab_comp_close_commute (c:comp) (x:var)
  : Lemma (elab_comp (close_comp c x) == RT.close_term (elab_comp c) x)
  = RT.close_term_spec (elab_comp c) x;
    elab_comp_close_commute' c x 0

let elab_comp_open_commute (c:comp) (x:term)
  : Lemma (elab_comp (open_comp_with c x) == RT.open_with (elab_comp c) x)
  = RT.open_with_spec (elab_comp c) x;
    elab_comp_open_commute' c x 0

let elab_ln t i = ()

let elab_ln_comp (c:comp) (i:int)
  : Lemma (requires ln_c' c i)
          (ensures RT.ln' (elab_comp c) i) =

  match c with
  | C_Tot t -> elab_ln t i
  | C_ST st ->
    elab_ln st.res i;
    elab_ln st.pre i;
    elab_ln st.post (i + 1)
  | C_STGhost inames st
  | C_STAtomic inames _ st ->
    elab_ln inames i;
    elab_ln st.res i;
    elab_ln st.pre i;
    elab_ln st.post (i + 1)

let elab_freevars_eq (e:term)
  : Lemma (Set.equal (freevars e) (RT.freevars e)) = ()

let elab_freevars_comp_eq (c:comp)
  : Lemma (Set.equal (freevars_comp c) (RT.freevars (elab_comp c))) =

  match c with
  | C_Tot t -> elab_freevars_eq t
  | C_ST st ->
    elab_freevars_eq st.res;
    elab_freevars_eq st.pre;
    elab_freevars_eq st.post
  | C_STGhost inames st
  | C_STAtomic inames _ st ->
    elab_freevars_eq inames;
    elab_freevars_eq st.res;
    elab_freevars_eq st.pre;
    elab_freevars_eq st.post
#pop-options

let elab_freevars e = elab_freevars_eq e
