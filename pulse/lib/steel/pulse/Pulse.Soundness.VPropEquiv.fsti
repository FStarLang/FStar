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

module Pulse.Soundness.VPropEquiv
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

val vprop_equiv_unit_soundness (#g:stt_env) (#v0 #v1:term) 
                               (d0:tot_typing g v0 tm_vprop)
                               (eq:vprop_equiv g v0 v1)
  : GTot (RT.tot_typing (elab_env g) (`())
            (stt_vprop_equiv (elab_term v0) (elab_term v1)))
