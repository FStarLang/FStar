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

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing  
module C = FStar.Stubs.TypeChecker.Core

module S = Pulse.Syntax
module RU = Pulse.RuntimeUtils


open FStar.Ghost


val admit_comp_typing (g:env) (c:comp_st)
  : comp_typing_u g c

let rt_equiv_typing (#g:_) (#t0 #t1:_) (d:RT.equiv g t0 t1)
                    (#k:_)
                    (d1:Ghost.erased (RT.tot_typing g t0 k))
  : Ghost.erased (RT.tot_typing g t1 k)
  = admit()

val st_typing_correctness_ctot (#g:env) (#t:st_term) (#c:comp{C_Tot? c}) 
                               (_:st_typing g t c)
  : (u:Ghost.erased universe & universe_of g (comp_res c) u)

let inames_of_comp_st (c:comp_st) =
  match c with
  | C_STAtomic _ _ _ -> comp_inames c
  | _ -> tm_emp_inames

let iname_typing (g:env) (c:comp_st) = tot_typing g (inames_of_comp_st c) tm_inames

val st_typing_correctness (#g:env) (#t:st_term) (#c:comp_st) 
                          (d:st_typing g t c)
  : comp_typing_u g c
  
val comp_typing_inversion (#g:env) (#c:comp_st) (ct:comp_typing_u g c)
  : st_comp_typing g (st_comp_of_comp c) & iname_typing g c

val st_comp_typing_inversion_cofinite (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre tm_vprop &
     (x:var{fresh_wrt x g (freevars st.post)} -> //this part is tricky, to get the quantification on x
       tot_typing (push_binding g x ppname_default st.res) (open_term st.post x) tm_vprop))

val st_comp_typing_inversion (#g:env) (#st:_) (ct:st_comp_typing g st)
  : (universe_of g st.res st.u &
     tot_typing g st.pre tm_vprop &
     x:var{fresh_wrt x g (freevars st.post)} &
     tot_typing (push_binding g x ppname_default st.res) (open_term st.post x) tm_vprop)

val tm_exists_inversion (#g:env) (#u:universe) (#ty:term) (#p:term) 
                        (_:tot_typing g (tm_exists_sl u (as_binder ty) p) tm_vprop)
                        (x:var { fresh_wrt x g (freevars p) } )
  : universe_of g ty u &
    tot_typing (push_binding g x ppname_default ty) p tm_vprop

val pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (tm_pure p) tm_vprop)
   : tot_typing g p (S.wr FStar.Reflection.Typing.tm_prop Range.range_0)

module RT = FStar.Reflection.Typing
val typing_correctness
  (#g:R.env) 
  (#t:R.term)
  (#ty:R.typ) 
  (#eff:_)
  (_:erased (RT.typing g t (eff, ty)))
  : erased (u:R.universe & RT.typing g ty (C.E_Total, RT.tm_type u))

let renaming x y = [NT x (tm_var {nm_index=y; nm_ppname=ppname_default})]
val tot_typing_renaming1
  (g:env) (x:var {None? (lookup g x)}) (tx e ty:term)
  (_:tot_typing (push_binding g x ppname_default tx) e ty)
  (y:var { None? (lookup g y) /\ x <> y })
  : tot_typing (push_binding g y ppname_default tx)
               (subst_term e (renaming x y))
               (subst_term ty (renaming x y))


val tot_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:term) (ty:typ) (_:tot_typing (push_env g g') t ty)
  (g1:env { pairwise_disjoint g g1 g' })
  : tot_typing (push_env (push_env g g1) g') t ty

val st_typing_weakening
  (g:env) (g':env { disjoint g g' })
  (t:st_term) (c:comp) (_:st_typing (push_env g g') t c)
  (g1:env { pairwise_disjoint g g1 g' })
  : st_typing (push_env (push_env g g1) g') t c

let veq_weakening
  (g:env) (g':env { disjoint g g' })
  (#v1 #v2:vprop) (_:vprop_equiv (push_env g g') v1 v2)
  (g1:env { pairwise_disjoint g g1 g' })
  : vprop_equiv (push_env (push_env g g1) g') v1 v2 = RU.magic ()

let nt (x:var) (t:term) = [ NT x t ]

val st_typing_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (#eff:T.tot_or_ghost)
  (e_typing:typing g e eff t)
  (#e1:st_term) (#c1:comp_st)
  (e1_typing:st_typing (push_env g (push_env (singleton_env (fstar_env g) x t) g')) e1 c1)
  (_:squash (eff == T.E_Ghost ==> C_STGhost? c1))

  : st_typing (push_env g (subst_env g' (nt x e)))
              (subst_st_term e1 (nt x e))
              (subst_comp c1 (nt x e))

let vprop_equiv_subst
  (g:env) (x:var) (t:typ) (g':env { pairwise_disjoint g (singleton_env (fstar_env g) x t) g' })
  (#e:term)
  (#eff:T.tot_or_ghost)
  (e_typing:typing g e eff t)
  (#p1:term) (#p2:term)
  (veq:vprop_equiv (push_env g (push_env (singleton_env (fstar_env g) x t) g')) p1 p2)

: vprop_equiv (push_env g (subst_env g' (nt x e)))
              (subst_term p1 (nt x e))
              (subst_term p2 (nt x e)) =
  admit ()
