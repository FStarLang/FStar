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

module Pulse.Soundness.STT

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing

open Pulse.Reflection.Util

let post_type t = mk_arrow (t, R.Q_Explicit) vprop_tm
let inames_tm = R.(pack_ln (Tv_FVar (pack_fv inames_lid)))

val stt_typing (#f:RT.fstar_env)//needs to bind stt
               (#u:R.universe)
               (#t:R.term)
               (#pre:R.term)
               (#post:R.term)
               (_:RT.tot_typing f t (RT.tm_type u))
               (_:RT.tot_typing f pre vprop_tm)
               (_:RT.tot_typing f post (post_type t))
  : GTot (RT.tot_typing f (mk_stt_comp u t pre post) (RT.tm_type RT.u_zero))

val stt_atomic_typing (#obs:R.term)
                      (#f:RT.fstar_env)//needs to bind stt
                      (#u:R.universe)
                      (#inames:R.term)
                      (#t:R.term)
                      (#pre:R.term)
                      (#post:R.term)
                      (_:RT.tot_typing f t (RT.tm_type u))
                      (_:RT.tot_typing f inames inames_tm)
                      (_:RT.tot_typing f pre vprop_tm)
                      (_:RT.tot_typing f post (post_type t))
  : GTot (RT.tot_typing f (mk_stt_atomic_comp obs u t inames pre post) (RT.tm_type (u_atomic_ghost u)))

val stt_ghost_typing (#f:RT.fstar_env)//needs to bind stt
                     (#u:R.universe)
                     (#t:R.term)
                     (#inames:R.term)
                     (#pre:R.term)
                     (#post:R.term)
                     (_:RT.tot_typing f t (RT.tm_type u))
                     (_:RT.tot_typing f inames inames_tm)
                     (_:RT.tot_typing f pre vprop_tm)
                     (_:RT.tot_typing f post (post_type t))
  : GTot (RT.tot_typing f (mk_stt_ghost_comp u t inames pre post) (RT.tm_type (u_atomic_ghost u)))
