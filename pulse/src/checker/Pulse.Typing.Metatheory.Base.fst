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
  = admit()

let admit_comp_typing (g:env) (c:comp_st)
  : comp_typing_u g c
  = match c with
    | C_ST st ->
      CT_ST g st (admit_st_comp_typing g st)
    | C_STAtomic inames obs st ->
      CT_STAtomic g inames obs st (admit()) (admit_st_comp_typing g st)
    | C_STGhost inames st ->
      CT_STGhost g inames st (admit ()) (admit_st_comp_typing g st)      

let st_typing_correctness_ctot (#g:env) (#t:st_term) (#c:comp{C_Tot? c}) 
                               (_:st_typing g t c)
: (u:Ghost.erased universe & universe_of g (comp_res c) u)
= let u : Ghost.erased universe = RU.magic () in
  let ty : universe_of g (comp_res c) u = RU.magic() in
  (| u, ty |)    

let st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (_:st_typing g t c)
  : comp_typing_u g c
  = admit_comp_typing g c
    
let add_frame_well_typed (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
                         (#f:term) (ft:tot_typing g f tm_slprop)
  : Dv (comp_typing_u g (add_frame c f))
  = admit_comp_typing _ _

let emp_inames_typing (g:env) : tot_typing g tm_emp_inames tm_inames = RU.magic()

let comp_typing_inversion #g #c ct = 
  match ct with
  | CT_ST _ _ st -> st, emp_inames_typing g
  | CT_STGhost _ _ _ it st
  | CT_STAtomic _ _ _ _ it st -> st, it

let st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st) = 
  admit(), admit(), (fun _ -> admit())

let stc_ty  (#g:env) (#st:_) (ct:st_comp_typing g st) : universe_of g st.res st.u = 
 let STC g st x ty pre post = ct in ty
let stc_pre (#g:env) (#st:_) (ct:st_comp_typing g st) : tot_typing g st.pre tm_slprop = 
  let STC g st x ty pre post = ct in pre
let stc_x (#g:env) (#st:_) (ct:st_comp_typing g st) : x:Ghost.erased var{fresh_wrt x g (freevars st.post)} = 
  let STC g st x ty pre post = ct in Ghost.hide x 
let stc_post (#g:env) (#st:_) (ct:st_comp_typing g st) 
  : tot_typing (push_binding g (stc_x ct) ppname_default st.res) 
               (open_term st.post (stc_x ct)) tm_slprop =
  let STC g st x ty pre post = ct in
  post
let st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st) = 
   (| stc_ty ct, stc_pre ct, stc_x ct, stc_post ct |)

let st_comp_typing_inversion_with_name (#g:env) (#st:_) (ct:st_comp_typing g st) (x:var{fresh_wrt x g (freevars st.post)})
: (universe_of g st.res st.u &
   tot_typing g st.pre tm_slprop &
   tot_typing (push_binding g x ppname_default st.res) (open_term st.post x) tm_slprop)
= assume (x == Ghost.reveal <| stc_x ct);
  (stc_ty ct, stc_pre ct, stc_post ct)

let tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (tm_exists_sl u (as_binder ty) p) tm_slprop)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ppname_default ty) p tm_slprop
  = admit(), admit()

let pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (tm_pure p) tm_slprop)
   : tot_typing g p (wr FStar.Reflection.Typing.tm_prop Range.range_0)
   = admit ()

let typing_correctness _ = admit()
let tot_typing_renaming1 _ _ _ _ _ _ = admit()
let tot_typing_weakening _ _ _ _ _ _ = admit ()

let non_informative_t_weakening (g g':env) (g1:env{ pairwise_disjoint g g1 g' })
  (u:universe) (t:term)
  (d:non_informative_t (push_env g g') u t)
  : non_informative_t (push_env (push_env g g1) g') u t =
  let (| w, _ |) = d in
  (| w, RU.magic #(tot_typing _ _ _) () |)

let non_informative_c_weakening (g g':env) (g1:env{ pairwise_disjoint g g1 g' })
  (c:comp_st)
  (d:non_informative_c (push_env g g') c)
  : non_informative_c (push_env (push_env g g1) g') c =
  non_informative_t_weakening g g' g1 _ _ d

let bind_comp_weakening (g:env) (g':env { disjoint g g' })
  (#x:var) (#c1 #c2 #c3:comp) (d:bind_comp (push_env g g') x c1 c2 c3)
  (g1:env { pairwise_disjoint g g1 g' })
  : bind_comp (push_env (push_env g g1) g') x c1 c2 c3
  = admit()

let lift_comp_weakening (g:env) (g':env { disjoint g g'})
  (#c1 #c2:comp) (d:lift_comp (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : Tot (lift_comp (push_env (push_env g g1) g') c1 c2)
        (decreases d) =
  
  match d with
  | Lift_STAtomic_ST _ c -> Lift_STAtomic_ST _ c
  | Lift_Ghost_Neutral _ c non_informative_c ->
    Lift_Ghost_Neutral _ c (non_informative_c_weakening g g' g1 _ non_informative_c)
  | Lift_Neutral_Ghost _ c -> Lift_Neutral_Ghost _ c
  | Lift_Observability _ obs c -> Lift_Observability _ obs c

// TODO: the proof for RT.Equiv is not correct here
let equiv_weakening (g:env) (g':env { disjoint g g' })
  #t1 #t2 (d:RT.equiv (elab_env (push_env g g')) t1 t2)
  (g1:env { pairwise_disjoint g g1 g' })
  : RT.equiv (elab_env (push_env (push_env g g1) g')) t1 t2 =
  admit ();
  d

let st_equiv_weakening (g:env) (g':env { disjoint g g' })
  (#c1 #c2:comp) (d:st_equiv (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_equiv (push_env (push_env g g1) g') c1 c2 =
  match d with
  | ST_SLPropEquiv _ c1 c2 x _ _ _ hequiv _ _ ->
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    ST_SLPropEquiv _ c1 c2 x (RU.magic ()) (RU.magic ()) (RU.magic ())
      (equiv_weakening _ _ hequiv _) (RU.magic ()) (RU.magic ())
  | ST_TotEquiv _ t1 t2 u _ _ ->
    ST_TotEquiv _ t1 t2 u (RU.magic ()) (RU.magic ())

// TODO: add precondition that g1 extends g'
let prop_validity_token_weakening (#g:env) (#t:term)
  (token:prop_validity g t)
  (g1:env)
  : prop_validity g1 t =
  admit ();
  token

let rec st_sub_weakening (g:env) (g':env { disjoint g g' })
  (#c1 #c2:comp) (d:st_sub (push_env g g') c1 c2)
  (g1:env { pairwise_disjoint g g1 g' })
  : Tot (st_sub (push_env (push_env g g1) g') c1 c2)
        (decreases d)
=
  let g'' = push_env (push_env g g1) g' in
  match d with
  | STS_Refl _ _ ->
    STS_Refl _ _
  | STS_Trans _ _ _ _ dl dr ->
    STS_Trans _ _ _ _ (st_sub_weakening g g' dl g1) (st_sub_weakening g g' dr g1)
  | STS_GhostInvs _ stc is1 is2 tok ->
    let tok : prop_validity g'' (tm_inames_subset is1 is2) = prop_validity_token_weakening tok g'' in
    STS_GhostInvs g'' stc is1 is2 tok
  | STS_AtomicInvs _ stc is1 is2 o1 o2 tok ->
    let tok : prop_validity g'' (tm_inames_subset is1 is2) = prop_validity_token_weakening tok g'' in
    STS_AtomicInvs g'' stc is1 is2 o1 o2 tok

let st_comp_typing_weakening (g:env) (g':env { disjoint g g' })
  (#s:st_comp) (d:st_comp_typing (push_env g g') s)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_comp_typing (push_env (push_env g g1) g') s =
  match d with
  | STC _ st x _ _ _ ->
    assume (~ (x `Set.mem` dom g'));
    assume (~ (x `Set.mem` dom g1));
    STC _ st x (RU.magic ()) (RU.magic ()) (RU.magic ())

let comp_typing_weakening (g:env) (g':env { disjoint g g' })
  (#c:comp) (#u:universe) (d:comp_typing (push_env g g') c u)
  (g1:env { pairwise_disjoint g g1 g' })
  : comp_typing (push_env (push_env g g1) g') c u =
  match d with
  | CT_Tot _ t u _ -> CT_Tot _ t u (RU.magic ())
  | CT_ST _ _ d -> CT_ST _ _ (st_comp_typing_weakening g g' d g1)
  | CT_STAtomic _ inames obs _ _ d ->
    CT_STAtomic _ inames obs _ (RU.magic ()) (st_comp_typing_weakening g g' d g1)
  | CT_STGhost _ inames _ _ d ->
    CT_STGhost _ inames _ (RU.magic ()) (st_comp_typing_weakening g g' d g1)

#push-options "--split_queries no --z3rlimit_factor 8 --fuel 1 --ifuel 1"
let st_typing_weakening g g' t c d g1
  : st_typing (push_env (push_env g g1) g') t c
  = admit () 
#pop-options