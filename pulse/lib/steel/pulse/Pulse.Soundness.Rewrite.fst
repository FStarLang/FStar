module Pulse.Soundness.Rewrite

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Soundness.Common

module RT = FStar.Reflection.Typing
module WT = Pulse.Steel.Wrapper.Typing

let rewrite_soundness
  (#f:stt_env)
		(#g:env)
		(#t:st_term)
		(#c:comp)
		(d:st_typing f g t c{T_Rewrite? d})
		: GTot (RT.tot_typing (extend_env_l f g)
                          (elab_st_typing d)
                          (elab_comp c)) =
		
		let T_Rewrite _ p q p_typing equiv_p_q = d in
		let rp = elab_term p in
		let rq = elab_term q in
		let rp_typing : RT.tot_typing _ rp vprop_tm =
		  tot_typing_soundness p_typing in
		let rq_typing : RT.tot_typing _ rq vprop_tm =
		  tot_typing_soundness (let f, _ = vprop_equiv_typing _ _ _ _ equiv_p_q in
				                      f p_typing) in
		let d_stt_vprop_equiv =
		  Pulse.Soundness.VPropEquiv.vprop_equiv_unit_soundness
				  p_typing equiv_p_q in
		
		WT.rewrite_typing rp_typing rq_typing d_stt_vprop_equiv
