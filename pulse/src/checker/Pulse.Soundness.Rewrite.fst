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

module Pulse.Soundness.Rewrite

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Soundness.Common
open Pulse.Checker.VPropEquiv

module RT = FStar.Reflection.Typing
module WT = Pulse.Lib.Core.Typing

let rewrite_soundness
  		(#g:stt_env)
		(#t:st_term)
		(#c:comp)
		(d:st_typing g t c{T_Rewrite? d})
		: GTot (RT.tot_typing (elab_env g)
							  (elab_st_typing d)
							  (elab_comp c)) =
		
		let T_Rewrite _ p q p_typing equiv_p_q = d in
		let rp_typing : RT.tot_typing _ p vprop_tm =
		  tot_typing_soundness p_typing in
		let rq_typing : RT.tot_typing _ q vprop_tm =
		  tot_typing_soundness (let f, _ = vprop_equiv_typing equiv_p_q in
				                      f p_typing) in
		let d_stt_vprop_equiv =
		  Pulse.Soundness.VPropEquiv.vprop_equiv_unit_soundness
				  p_typing equiv_p_q in
		
		WT.rewrite_typing rp_typing rq_typing d_stt_vprop_equiv
