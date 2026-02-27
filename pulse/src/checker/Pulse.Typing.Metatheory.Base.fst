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

module Pulse.Typing.Metatheory.Base
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing
module RU = Pulse.RuntimeUtils
module RT = FStar.Reflection.Typing

let admit_st_comp_typing (g:env) (st:st_comp) 
  : st_comp_typing g st
  = ()

let admit_comp_typing (g:env) (c:comp_st)
  : comp_typing_u g c
  = ()

let st_typing_correctness_ctot (g:env) (t:st_term) (c:comp{C_Tot? c}) 
                               (_:st_typing g t c)
: Ghost.erased universe
= let u : Ghost.erased universe = RU.magic () in
  u

let st_typing_correctness (g:env) (t:st_term) (c:comp_st) 
                          (_:st_typing g t c)
  : comp_typing_u g c
  = ()
    
let add_frame_well_typed (g:env) (c:comp_st) (ct:comp_typing_u g c)
                         (f:term) (ft:tot_typing g f tm_slprop)
  : Dv (comp_typing_u g (add_frame c f))
  = ()

let emp_inames_typing (g:env) : tot_typing g tm_emp_inames tm_inames = ()

let comp_typing_inversion g c ct = 
  ((), ())

let st_comp_typing_inversion_cofinite (g:env) (st:st_comp) (ct:st_comp_typing g st) = 
  (), (), (fun _ -> ())

let stc_x   (g:env) (st:st_comp) (ct:st_comp_typing g st) : x:Ghost.erased var{fresh_wrt x g (freevars st.post)} = admit()

let st_comp_typing_inversion (g:env) (st:st_comp) (ct:st_comp_typing g st) = 
   (| (), (), stc_x g st ct, () |)

let st_comp_typing_inversion_with_name (g:env) (st:st_comp) (ct:st_comp_typing g st) (x:var{fresh_wrt x g (freevars st.post)})
: (universe_of g st.res st.u &
   tot_typing g st.pre tm_slprop &
   tot_typing (push_binding g x ppname_default st.res) (open_term st.post x) tm_slprop)
= ((), (), ())

let tm_exists_inversion (g:env) (u:universe) (ty:term) (p:term) 
                        (_:tot_typing g (tm_exists_sl u (as_binder ty) p) tm_slprop)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ppname_default ty) p tm_slprop
  = (), ()

let pure_typing_inversion (g:env) (p:term) (_:tot_typing g (tm_pure p) tm_slprop)
   : tot_typing g p (wr FStar.Reflection.Typing.tm_prop Range.range_0)
   = ()

let typing_correctness _ = admit()
let tot_typing_renaming1 _ _ _ _ _ _ = admit()
let tot_typing_weakening _ _ _ _ _ _ = admit ()

let non_informative_t_weakening (g g':env) (g1:env{ pairwise_disjoint g g1 g' })
  (u:universe) (t:term)
  (d:non_informative_t (push_env g g') u t)
  : non_informative_t (push_env (push_env g g1) g') u t =
  d

let non_informative_c_weakening (g g':env) (g1:env{ pairwise_disjoint g g1 g' })
  (c:comp_st)
  (d:non_informative_c (push_env g g') c)
  : non_informative_c (push_env (push_env g g1) g') c =
  non_informative_t_weakening g g' g1 _ _ d

let bind_comp_weakening (g:env) (g':env { disjoint g g' })
  (x:var) (c1 c2 c3:comp) (d:bind_comp (push_env g g') x c1 c2 c3)
  (g1:env { pairwise_disjoint g g1 g' })
  : bind_comp (push_env (push_env g g1) g') x c1 c2 c3
  = ()

let lift_comp_weakening (g:env) (g':env { disjoint g g'})
  (c1 c2:comp) (d:lift_comp (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : lift_comp (push_env (push_env g g1) g') c1 c2
  = ()

// TODO: the proof for RT.Equiv is not correct here
let equiv_weakening (g:env) (g':env { disjoint g g' })
  #t1 #t2 (d:RT.equiv (elab_env (push_env g g')) t1 t2)
  (g1:env { pairwise_disjoint g g1 g' })
  : RT.equiv (elab_env (push_env (push_env g g1) g')) t1 t2 =
  admit ();
  d

let st_equiv_weakening (g:env) (g':env { disjoint g g' })
  (c1 c2:comp) (d:st_equiv (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_equiv (push_env (push_env g g1) g') c1 c2 =
  ()

// TODO: add precondition that g1 extends g'
let prop_validity_token_weakening (#g:env) (#t:term)
  (token:prop_validity g t)
  (g1:env)
  : prop_validity g1 t =
  admit ();
  token

let st_sub_weakening (g:env) (g':env { disjoint g g' })
  (c1 c2:comp) (d:st_sub (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_sub (push_env (push_env g g1) g') c1 c2
  = ()

let st_comp_typing_weakening (g:env) (g':env { disjoint g g' })
  (s:st_comp) (d:st_comp_typing (push_env g g') s)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_comp_typing (push_env (push_env g g1) g') s =
  ()

let comp_typing_weakening (g:env) (g':env { disjoint g g' })
  (c:comp) (u:universe) (d:comp_typing (push_env g g') c u)
  (g1:env { pairwise_disjoint g g1 g' })
  : comp_typing (push_env (push_env g g1) g') c u =
  ()

let st_typing_weakening g g' t c d g1
  : st_typing (push_env (push_env g g1) g') t c
  = ()