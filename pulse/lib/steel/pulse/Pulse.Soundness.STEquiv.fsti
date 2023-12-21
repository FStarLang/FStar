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

module Pulse.Soundness.STEquiv
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

val st_equiv_soundness (g:stt_env)
                       (c0 c1:ln_comp) 
                       (d:st_equiv g c0 c1)
                       (r:R.term)
                       (d_r:RT.tot_typing (elab_env g) r (elab_comp c0)) 
  : GTot (RT.tot_typing (elab_env g) (elab_sub c0 c1 r) (elab_comp c1))
