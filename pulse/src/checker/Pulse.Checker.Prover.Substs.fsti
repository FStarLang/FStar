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
open Pulse.PP
open Pulse.Show

module L = FStar.List.Tot
module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

module Env = Pulse.Typing.Env

val ss_t : Type0

instance val pp_ss_t : printable ss_t
instance val showable_ss_t : tac_showable ss_t

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

val lemma_subst_empty_term (t:term)
  : Lemma (ss_term t empty == t)
          [SMTPat (ss_term t empty)]

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
