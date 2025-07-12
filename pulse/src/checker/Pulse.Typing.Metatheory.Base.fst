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

let non_informative_t_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (u:universe) (t1:term)
  (d:non_informative_t (push_env g (push_env (singleton_env (fstar_env g) x t) g')) u t1)

  : non_informative_t (push_env g (subst_env g' (nt x e))) u (subst_term t1 (nt x e)) =

  let ss = nt x e in

  let (| w, _ |) = d in
  (| subst_term w ss, RU.magic #(tot_typing _ _ _) () |)

let non_informative_c_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (c:comp_st)
  (d:non_informative_c (push_env g (push_env (singleton_env (fstar_env g) x t) g')) c)

  : non_informative_c (push_env g (subst_env g' (nt x e))) (subst_comp c (nt x e)) =

  non_informative_t_subst g x t g' e_typing _ _ d

let lift_comp_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#c1 #c2:comp)
  (d:lift_comp (push_env g (push_env (singleton_env (fstar_env g) x t) g')) c1 c2)

  : lift_comp (push_env g (subst_env g' (nt x e)))
              (subst_comp c1 (nt x e))
              (subst_comp c2 (nt x e)) =

  let ss = nt x e in
  
  match d with
  | Lift_STAtomic_ST _ c ->
    Lift_STAtomic_ST _ (subst_comp c ss)

  | Lift_Ghost_Neutral _ c d_non_informative ->
    Lift_Ghost_Neutral _ (subst_comp c ss)
      (non_informative_c_subst g x t g' e_typing _ d_non_informative)
  
  | Lift_Neutral_Ghost _ c ->
    Lift_Neutral_Ghost _ (subst_comp c ss)
  
  | Lift_Observability _ c o ->
    Lift_Observability _ (subst_comp c ss) o

let bind_comp_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#y:var) (#c1 #c2 #c3:comp_st) (d:bind_comp (push_env g (push_env (singleton_env (fstar_env g) x t) g')) y c1 c2 c3)
  : bind_comp (push_env g (subst_env g' (nt x e)))
              y
              (subst_comp c1 (nt x e))
              (subst_comp c2 (nt x e))
              (subst_comp c3 (nt x e)) =
  
  let ss = nt x e in

  match d with
  | Bind_comp _ y c1 c2 _ z _ ->
    assume bind_comp_pre y (S.subst_comp c1 ss) (S.subst_comp c2 ss);
    assume None? (lookup (push_env g (subst_env g' (nt x e))) z) /\
        ~(Set.mem z (S.freevars (S.comp_post (S.subst_comp c2 ss))));
    Bind_comp _ y (subst_comp c1 ss)
                  (subst_comp c2 ss)
                  (RU.magic ())
                  z
                  (RU.magic ())


let st_equiv_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#c1 #c2:comp) (d:st_equiv (push_env g (push_env (singleton_env (fstar_env g) x t) g')) c1 c2)
  : st_equiv (push_env g (subst_env g' (nt x e)))
             (subst_comp c1 (nt x e))
             (subst_comp c2 (nt x e)) =
  match d with
  | ST_SLPropEquiv _ c1 c2 y _ _ _ hequiv _ _ ->
    assume None? (lookup (push_env g (subst_env g' (nt x e))) y) /\
        ~(Set.mem y (S.freevars (S.comp_post (S.subst_comp c1 (nt x e))))) /\
        ~(Set.mem y (S.freevars (S.comp_post (S.subst_comp c2 (nt x e)))));
    ST_SLPropEquiv _ (subst_comp c1 (nt x e))
                    (subst_comp c2 (nt x e))
                    y
                    (RU.magic ())
                    (RU.magic ())
                    (RU.magic ())
                    (admit (); hequiv)  // TODO: incorrect proof
                    (RU.magic ())
                    (RU.magic ())
  | ST_TotEquiv _ t1 t2 u _ _ ->
    ST_TotEquiv _ (subst_term t1 (nt x e)) (subst_term t2 (nt x e)) u (RU.magic ()) (RU.magic ())

let st_comp_typing_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#s:st_comp) (d:st_comp_typing (push_env g (push_env (singleton_env (fstar_env g) x t) g')) s)
  : st_comp_typing (push_env g (subst_env g' (nt x e)))
                   (subst_st_comp s (nt x e)) =
  match d with
  | STC _ s y _ _ _ ->
    assume None? (lookup (push_env g (subst_env g' (nt x e))) y) /\
        ~(Set.mem y (S.freevars (S.subst_st_comp s (nt x e)).post));
    STC _ (subst_st_comp s (nt x e))
         y
         (RU.magic ())
         (RU.magic ())
         (RU.magic ())

let comp_typing_subst (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (e_typing:tot_typing g e t)
  (#c:comp) (#u:universe) (d:comp_typing (push_env g (push_env (singleton_env (fstar_env g) x t) g')) c u)
  : comp_typing (push_env g (subst_env g' (nt x e)))
                (subst_comp c (nt x e)) u =
  match d with
  | CT_Tot _ t u _ ->
    CT_Tot _ (subst_term t (nt x e)) u (RU.magic ())
  | CT_ST _ s d_s ->
    CT_ST _ (subst_st_comp s (nt x e)) (st_comp_typing_subst g x t g' e_typing d_s)
  | CT_STAtomic _ inames obs s _ d_s ->
    CT_STAtomic _ (subst_term inames (nt x e)) obs (subst_st_comp s (nt x e)) (RU.magic ()) (st_comp_typing_subst g x t g' e_typing d_s)
  | CT_STGhost _ inames s _ d_s ->
    CT_STGhost _ (subst_term inames (nt x e)) (subst_st_comp s (nt x e)) (RU.magic ()) (st_comp_typing_subst g x t g' e_typing d_s)
  

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b { y == x } = x

let st_typing_subst g x t g' #e #eff e_typing #e1 #c1 e1_typing _
  : Tot (st_typing (push_env g (subst_env g' (nt x e)))
                   (subst_st_term e1 (nt x e))
                   (subst_comp c1 (nt x e))) = admit()