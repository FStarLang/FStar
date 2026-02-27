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

module Pulse.Elaborate.Core

open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing

module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2

module S = Pulse.Syntax
module RU = Pulse.RuntimeUtils
module T = FStar.Tactics.V2
open Pulse.Reflection.Util

let elab_frame (c:comp_st) (frame:term) (e:R.term) =
  let u = comp_u c in
  let ty = comp_res c in
  let pre = comp_pre c in
  let post = comp_post c in
  if C_ST? c
  then mk_frame_stt u ty pre (mk_abs ty R.Q_Explicit post) frame e
  else if C_STAtomic? c
  then let opened = comp_inames c in
       mk_frame_stt_atomic u ty opened pre (mk_abs ty R.Q_Explicit post) frame e
  else mk_frame_stt_ghost u ty pre (mk_abs ty R.Q_Explicit post) frame e

let elab_sub (c1 c2:comp_st) (e:R.term) =
  let ty = comp_res c1 in
  let u = comp_u c1 in
  let pre1 = comp_pre c1 in
  let pre2 = comp_pre c2 in
  let post1 = mk_abs ty R.Q_Explicit (comp_post c1) in
  let post2 = mk_abs ty R.Q_Explicit (comp_post c2) in
  if C_ST? c1
  then mk_sub_stt u ty pre1 pre2 post1 post2 e
  else if C_STAtomic? c1
  then let opened = comp_inames c1 in
       mk_sub_stt_atomic u ty opened pre1 pre2 post1 post2 e
  else mk_sub_stt_ghost u ty pre1 pre2 post1 post2 e


let elab_bind #g #x #c1 #c2 #c
              (bc:bind_comp g x c1 c2 c)
              (e1 e2:R.term)
  : GTot R.term
  = RU.magic ()
  
let elab_lift #g #c1 #c2 (d:lift_comp g c1 c2) (e:R.term)
  : GTot R.term
  = RU.magic ()

let intro_pure_tm (p:term) =
  let open Pulse.Reflection.Util in
  let rng = R.range_of_term p in
  wtag (Some STT_Ghost) 
       (Tm_ST
        { t = T.mk_app
                (tm_pureapp (tm_fvar (as_fv (mk_pulse_lib_core_lid "intro_pure")))
                       None
                       p)
                [S.wr (`()) rng, T.Q_Explicit];
          args = [] })

let simple_arr (t1 t2 : R.term) : R.term =
  let b = R.pack_binder {
           sort = t1;
           ppname = Sealed.seal "x";
           qual = R.Q_Explicit;
           attrs = [] } in
  R.pack_ln (R.Tv_Arrow b (R.pack_comp (R.C_Total t2)))

let elab_st_sub (#g:env) (#c1 #c2 : comp)
     (d_sub : st_sub g c1 c2)
   : Tot (t:R.term
          & RT.tot_typing (elab_env g) t (simple_arr (elab_comp c1) (elab_comp c2)))
= RU.magic_s "elab_st_sub"

let rec elab_st_typing (#g:env)
                       (#t:st_term)
                       (#c:comp)
                       (d:st_typing g t c)
  : GTot R.term (decreases d)
  = RU.magic ()

and elab_br (#g:env)
            (#c:comp_st)
            (#sc_u:universe) (#sc_ty:typ) (#sc:term)
            (#p:pattern)
            (#e:st_term)
            (d : br_typing g sc_u sc_ty sc p e c)
  : GTot R.branch (decreases d)
  = RU.magic ()
and elab_branches (#g:env)
                  (#c:comp_st)
                  (#sc_u:universe) (#sc_ty:typ) (#sc:term)
                  (#brs:list branch)
                  (d : brs_typing g sc_u sc_ty sc brs c)
  : GTot (list R.branch)
        (decreases d)
  = RU.magic ()
