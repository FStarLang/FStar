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

module Pulse.Checker.Prover.Substs

open FStar.List.Tot

open Pulse.Syntax
open Pulse.Typing.Env
open Pulse.Typing

module L = FStar.List.Tot
module T = FStar.Tactics
module RT = FStar.Reflection.Typing

module Env = Pulse.Typing.Env

val ss_t : Type0

val ln_ss_t (s:ss_t) : bool
val as_map (ss:ss_t) : Map.t var term

let dom (ss:ss_t) = Map.domain (as_map ss)
let contains (ss:ss_t) (x:var) = Map.contains (as_map ss) x
let sel (ss:ss_t) (x:var { contains ss x }) = Map.sel (as_map ss) x

val empty : ss_t

val lemma_dom_empty ()
  : Lemma (dom empty == Set.empty)

val push (ss:ss_t) (x:var { ~ (contains ss x) }) (t:term) : ss_t

val push_ss (ss1:ss_t) (ss2:ss_t { Set.disjoint (dom ss1) (dom ss2) }) : ss_t

val check_disjoint (ss1 ss2:ss_t) : b:bool { b ==> Set.disjoint (dom ss1) (dom ss2) }
val diff (ss1 ss2:ss_t) : ss:ss_t { Set.disjoint (dom ss) (dom ss2) }

val push_as_map (ss1 ss2:ss_t)
  : Lemma (requires Set.disjoint (dom ss1) (dom ss2))
          (ensures as_map (push_ss ss1 ss2) == Map.concat (as_map ss1) (as_map ss2))
          [SMTPat (as_map (push_ss ss1 ss2))]

val ss_term (t:term) (ss:ss_t) : term
val ss_st_term (t:st_term) (ss:ss_t) : st_term
val ss_st_comp (s:st_comp) (ss:ss_t) : st_comp
val ss_comp (c:comp) (ss:ss_t) : comp
val ss_binder (b:binder) (ss:ss_t) : binder
val ss_env (g:env) (ss:ss_t)
  : g':env { fstar_env g' == fstar_env g /\
             Env.dom g' == Env.dom g }

val ss_st_comp_commutes (s:st_comp) (ss:ss_t)
  : Lemma (ensures
             ss_st_comp s ss ==
             { s with res = ss_term s.res ss;
                      pre = ss_term s.pre ss;
                      post = ss_term s.post ss; })  // no shifting required
          [SMTPat (ss_st_comp s ss)]

val ss_comp_commutes (c:comp) (ss:ss_t)
  : Lemma (ensures
             (let r = ss_comp c ss in
              (C_Tot? c ==> r == C_Tot (ss_term (comp_res c) ss)) /\
              (C_ST? c ==> r == C_ST (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STAtomic? c ==> r == C_STAtomic (ss_term (comp_inames c) ss)
                                                 (C_STAtomic?.obs c)
                                                 (ss_st_comp (st_comp_of_comp c) ss)) /\
              (C_STGhost? c ==> r == C_STGhost (ss_term (comp_inames c) ss)
                                               (ss_st_comp (st_comp_of_comp c) ss))))
          [SMTPat (ss_comp c ss)]

type nt_substs = l:list subst_elt { forall elt. L.memP elt l ==> RT.NT? elt }

let nt_subst_term (t:term) (ss:nt_substs) : term =
  L.fold_left (fun t elt -> subst_term t [elt]) t ss

let nt_subst_binder (b:binder) (ss:nt_substs) : binder =
  L.fold_left (fun b elt -> subst_binder b [elt]) b ss

let nt_subst_st_term (t:st_term) (ss:nt_substs) : st_term =
  L.fold_left (fun t elt -> subst_st_term t [elt]) t ss

let nt_subst_st_comp (s:st_comp) (ss:nt_substs) : st_comp =
  L.fold_left (fun s elt -> subst_st_comp s [elt]) s ss

let nt_subst_comp (c:comp) (ss:nt_substs) : comp =
  L.fold_left (fun c elt -> subst_comp c [elt]) c ss

let nt_subst_env (g:env) (ss:nt_substs) : g':env { Env.dom g' == Env.dom g /\
                                                   Env.fstar_env g' == Env.fstar_env g } =
  let g' = L.fold_left (fun g elt -> subst_env g [elt]) g ss in
  assume (Env.dom g' == Env.dom g /\ Env.fstar_env g' == Env.fstar_env g);
  g'

val nt_substs_st_comp_commutes (s:st_comp) (nts:nt_substs)
  : Lemma (ensures
             nt_subst_st_comp s nts ==
             { s with res = nt_subst_term s.res nts;
                      pre = nt_subst_term s.pre nts;
                      post = nt_subst_term s.post nts; })  // no shifting required
          [SMTPat (nt_subst_st_comp s nts)]

val nt_subst_comp_commutes (c:comp) (nts:nt_substs)
  : Lemma (ensures
             (let r = nt_subst_comp c nts in
              (C_Tot? c ==> r == C_Tot (nt_subst_term (comp_res c) nts)) /\
              (C_ST? c ==> r == C_ST (nt_subst_st_comp (st_comp_of_comp c) nts)) /\
              (C_STAtomic? c ==> r == C_STAtomic (nt_subst_term (comp_inames c) nts)
                                                  (C_STAtomic?.obs c)
                                                 (nt_subst_st_comp (st_comp_of_comp c) nts)) /\
              (C_STGhost? c ==> r == C_STGhost (nt_subst_term (comp_inames c) nts)
                                               (nt_subst_st_comp (st_comp_of_comp c) nts))))
          [SMTPat (nt_subst_comp c nts)]

let rec well_typed_nt_substs
  (g:env)
  (uvs:env)
  (nts:nt_substs)
  (effect_labels:list T.tot_or_ghost)
  : Tot Type0 (decreases L.length nts) =
  
  match bindings uvs, nts, effect_labels with
  | [], [], [] -> True
  | _::_, (RT.NT x e)::nts_rest, eff::effect_labels_rest ->
    let y, ty, rest_uvs = remove_binding uvs in
    x == y /\
    typing g e eff ty /\
    well_typed_nt_substs g (subst_env rest_uvs [ RT.NT x e ]) nts_rest effect_labels_rest
  | _, _, _ -> False

val is_permutation (nts:nt_substs) (ss:ss_t) : Type0

val ss_to_nt_substs (g:env) (uvs:env) (ss:ss_t)
  : T.Tac (either (nts:nt_substs &
                   effect_labels:list T.tot_or_ghost {
                     well_typed_nt_substs g uvs nts effect_labels /\
                     is_permutation nts ss
                   })
                  string)

val well_typed_nt_substs_prefix
  (g:env)
  (uvs:env)
  (nts:nt_substs)
  (effect_labels:list T.tot_or_ghost)
  (uvs1:env)
  : Pure (nt_substs & list T.tot_or_ghost)
         (requires well_typed_nt_substs g uvs nts effect_labels /\ env_extends uvs uvs1)
         (ensures fun (nts1, effect_labels1) -> well_typed_nt_substs g uvs1 nts1 effect_labels1)

val ss_nt_subst (g:env) (uvs:env) (ss:ss_t) (nts:nt_substs) (effect_labels:list T.tot_or_ghost)
  : Lemma
      (requires
         disjoint uvs g /\
         well_typed_nt_substs g uvs nts effect_labels /\
         is_permutation nts ss)
      (ensures
         (forall (t:term). nt_subst_term t nts == ss_term t ss) /\
         (forall (b:binder). nt_subst_binder b nts == ss_binder b ss) /\
         (forall (t:st_term). nt_subst_st_term t nts == ss_st_term t ss) /\
         (forall (c:comp). nt_subst_comp c nts == ss_comp c ss) /\
         (forall (s:st_comp). nt_subst_st_comp s nts == ss_st_comp s ss))
      [SMTPat (well_typed_nt_substs g uvs nts effect_labels); SMTPat (is_permutation nts ss)]

//
// Inr returns a (uvar, solution) where solution is ghost, expected tot
//
val st_typing_nt_substs
  (g:env) (uvs:env) (g':env { pairwise_disjoint g uvs g' })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g (push_env uvs g')) t c)
  (ss:nt_substs)
  (effect_labels:list T.tot_or_ghost { well_typed_nt_substs g uvs ss effect_labels })
: either
    (st_typing (push_env g (nt_subst_env g' ss)) (nt_subst_st_term t ss) (nt_subst_comp c ss))
    (var & term)

// val st_typing_subst (g:env) (uvs:env { disjoint uvs g }) (t:st_term) (c:comp_st)
//   (d:st_typing (push_env g uvs) t c)
//   (ss:ss_t)

//   : T.Tac (option (st_typing g (ss_st_term t ss) (ss_comp c ss)))

val st_typing_nt_substs_derived
  (g:env) (uvs:env { disjoint uvs g })
  (#t:st_term) (#c:comp_st) (t_typing:st_typing (push_env g uvs) t c)
  (ss:nt_substs)
  (effect_labels:list T.tot_or_ghost { well_typed_nt_substs g uvs ss effect_labels })
: either (st_typing g (nt_subst_st_term t ss) (nt_subst_comp c ss)) (var & term)

val vprop_equiv_nt_substs_derived
  (g:env) (uvs:env { disjoint g uvs })
  (#p1 #p2:vprop) (veq:vprop_equiv (push_env g uvs) p1 p2)
  (ss:nt_substs)
  (effect_labels:list T.tot_or_ghost { well_typed_nt_substs g uvs ss effect_labels })
: vprop_equiv g (nt_subst_term p1 ss) (nt_subst_term p2 ss)
