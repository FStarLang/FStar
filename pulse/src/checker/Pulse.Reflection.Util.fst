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

module Pulse.Reflection.Util

module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils
open FStar.List.Tot

let u_two = RT.(u_succ (u_succ u_zero))
let u_three = RT.(u_succ (u_succ (u_succ u_zero)))
let u_four = RT.(u_succ (u_succ (u_succ (u_succ u_zero))))
let u_atomic_ghost u = (RT.u_max u_four u)

let pulse_lib_core = ["Pulse"; "Lib"; "Core"]
let mk_pulse_lib_core_lid s = pulse_lib_core@[s]

let pulse_lib_noninformative = ["Pulse"; "Lib"; "NonInformative"]
let mk_pulse_lib_noninformative_lid s = pulse_lib_noninformative@[s]

let tun = R.pack_ln R.Tv_Unknown
let unit_lid = R.unit_lid
let bool_lid = R.bool_lid
let int_lid  = R.int_lid
let erased_lid = ["FStar"; "Ghost"; "erased"]
let hide_lid = ["FStar"; "Ghost"; "hide"]
let reveal_lid = ["FStar"; "Ghost"; "reveal"]
let slprop_lid = mk_pulse_lib_core_lid "slprop"
let slprop_fv = R.pack_fv slprop_lid
let slprop_tm = R.pack_ln (R.Tv_FVar slprop_fv)
let emp_lid = mk_pulse_lib_core_lid "emp"
let unit_fv = R.pack_fv unit_lid
let unit_tm = R.pack_ln (R.Tv_FVar unit_fv)
let bool_fv = R.pack_fv bool_lid
let bool_tm = R.pack_ln (R.Tv_FVar bool_fv)
let nat_lid = ["Prims"; "nat"]
let nat_fv = R.pack_fv nat_lid
let nat_tm = R.pack_ln (R.Tv_FVar nat_fv)
let szt_lid = ["FStar"; "SizeT"; "t"]
let szt_fv = R.pack_fv szt_lid
let szt_tm = R.pack_ln (R.Tv_FVar szt_fv)
let szv_lid = ["FStar"; "SizeT"; "v"]
let szv_fv = R.pack_fv szv_lid
let szv_tm = R.pack_ln (R.Tv_FVar szv_fv)
let seq_lid = ["FStar"; "Seq"; "Base"; "seq"]
let seq_create_lid = ["FStar"; "Seq"; "Base"; "create"]
let tot_lid = ["Prims"; "Tot"]

let slprop_equiv_norm_tm = R.pack_ln (R.Tv_FVar (R.pack_fv (mk_pulse_lib_core_lid "slprop_equiv_norm")))
let slprop_equiv_fold_tm (s:string) = 
  let head = R.pack_ln (R.Tv_FVar (R.pack_fv (mk_pulse_lib_core_lid "slprop_equiv_fold"))) in
  let s = R.pack_ln (R.Tv_Const (R.C_String s)) in
  let t = R.pack_ln (R.Tv_App head (s, R.Q_Explicit)) in
  t
let slprop_equiv_unfold_tm (s:string) =
  let head = R.pack_ln (R.Tv_FVar (R.pack_fv (mk_pulse_lib_core_lid "slprop_equiv_unfold"))) in
  let s = R.pack_ln (R.Tv_Const (R.C_String s)) in
  let t = R.pack_ln (R.Tv_App head (s, R.Q_Explicit)) in
  t
let match_rewrite_tac_tm = R.pack_ln (R.Tv_FVar (R.pack_fv (mk_pulse_lib_core_lid "match_rewrite_tac")))

(* The "plicities" *)
let ex t : R.argv = (t, R.Q_Explicit)
let im t : R.argv = (t, R.Q_Implicit)

let tuple2_lid = ["FStar"; "Pervasives"; "Native"; "tuple2"]
let fst_lid = ["FStar"; "Pervasives"; "Native"; "fst"]
let snd_lid = ["FStar"; "Pervasives"; "Native"; "snd"]

let mk_tuple2 (u1 u2:R.universe) (a1 a2:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv tuple2_lid) [u1; u2]) in
  let t = pack_ln (Tv_App t (a1, Q_Explicit)) in
  pack_ln (Tv_App t (a2, Q_Explicit))

let mk_fst (u1 u2:R.universe) (a1 a2 e:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv fst_lid) [u1; u2]) in
  let t = pack_ln (Tv_App t (a1, Q_Implicit)) in
  let t = pack_ln (Tv_App t (a2, Q_Implicit)) in
  pack_ln (Tv_App t (e, Q_Explicit))
  
let mk_snd (u1 u2:R.universe) (a1 a2 e:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv snd_lid) [u1; u2]) in
  let t = pack_ln (Tv_App t (a1, Q_Implicit)) in
  let t = pack_ln (Tv_App t (a2, Q_Implicit)) in
  pack_ln (Tv_App t (e, Q_Explicit))

let true_tm = R.pack_ln (R.Tv_Const (R.C_True))
let false_tm = R.pack_ln (R.Tv_Const (R.C_False))

let star_lid = mk_pulse_lib_core_lid "op_Star_Star"

let mk_star (l r:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv star_lid)) in
  let t = pack_ln (Tv_App t (l, Q_Explicit)) in
  pack_ln (Tv_App t (r, Q_Explicit))

let pure_lid = mk_pulse_lib_core_lid "pure"
let exists_lid = mk_pulse_lib_core_lid "op_exists_Star"
let pulse_lib_forall = ["Pulse"; "Lib"; "Forall"]
let mk_pulse_lib_forall_lid s = pulse_lib_forall@[s]

let forall_lid = mk_pulse_lib_forall_lid "op_forall_Star"
let args_of (tms:list R.term) =
  List.Tot.map (fun x -> x, R.Q_Explicit) tms

let mk_pure (p:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv pure_lid)) in
  pack_ln (Tv_App t (p, Q_Explicit))

let uzero = R.pack_universe (R.Uv_Zero)
let uone = R.pack_universe (R.Uv_Succ uzero)

let pulse_lib_reference = ["Pulse"; "Lib"; "Reference"]
let mk_pulse_lib_reference_lid s = pulse_lib_reference@[s]

let mk_squash (u:R.universe) (ty:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv R.squash_qn) [u]) in
  pack_ln (Tv_App t (ty, Q_Explicit))

let mk_eq2 (u:R.universe) (ty e1 e2:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv R.eq2_qn) [u]) in
  let t = pack_ln (Tv_App t (ty, Q_Implicit)) in
  let t = pack_ln (Tv_App t (e1, Q_Explicit)) in
  pack_ln (Tv_App t (e2, Q_Explicit))

let stt_admit_lid = mk_pulse_lib_core_lid "stt_admit"
let mk_stt_admit (u:R.universe) (t pre post:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv stt_admit_lid) [u]) in
  let t = pack_ln (Tv_App t (t, Q_Explicit)) in
  let t = pack_ln (Tv_App t (pre, Q_Explicit)) in
  pack_ln (Tv_App t (post, Q_Explicit))

let stt_atomic_admit_lid = mk_pulse_lib_core_lid "stt_atomic_admit"
let mk_stt_atomic_admit (u:R.universe) (t pre post:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv stt_atomic_admit_lid) [u]) in
  let t = pack_ln (Tv_App t (t, Q_Explicit)) in
  let t = pack_ln (Tv_App t (pre, Q_Explicit)) in
  pack_ln (Tv_App t (post, Q_Explicit))

let stt_ghost_admit_lid = mk_pulse_lib_core_lid "stt_ghost_admit"
let mk_stt_ghost_admit (u:R.universe) (t pre post:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv stt_ghost_admit_lid) [u]) in
  let t = pack_ln (Tv_App t (t, Q_Explicit)) in
  let t = pack_ln (Tv_App t (pre, Q_Explicit)) in
  pack_ln (Tv_App t (post, Q_Explicit))

let elim_pure_lid = mk_pulse_lib_core_lid "elim_pure"

 //the thunked, value-type counterpart of the effect STT
let stt_lid = mk_pulse_lib_core_lid "stt"
let stt_fv = R.pack_fv stt_lid
let stt_tm = R.pack_ln (R.Tv_FVar stt_fv)
let mk_stt_comp (u:R.universe) (res pre post:R.term) : Tot R.term =
  let t = R.pack_ln (R.Tv_UInst stt_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (res, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let stt_atomic_lid = mk_pulse_lib_core_lid "stt_atomic"
let stt_atomic_fv = R.pack_fv stt_atomic_lid
let stt_atomic_tm = R.pack_ln (R.Tv_FVar stt_atomic_fv)
let mk_stt_atomic_comp (obs:R.term) (u:R.universe) (a inames pre post:R.term) =
  let head = stt_atomic_fv in
  let t = R.pack_ln (R.Tv_UInst head [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (obs, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (inames, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))


let stt_ghost_lid = mk_pulse_lib_core_lid "stt_ghost"
let stt_ghost_fv = R.pack_fv stt_ghost_lid
let stt_ghost_tm = R.pack_ln (R.Tv_FVar stt_ghost_fv)
let mk_stt_ghost_comp (u:R.universe) (a inames pre post:R.term) =
  let t = R.pack_ln (R.Tv_UInst stt_ghost_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (inames, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_ghost_comp_post_equiv (g:R.env) (u:R.universe) (a inames pre post1 post2:R.term)
  (posts_equiv:RT.equiv g post1 post2)
  : RT.equiv g (mk_stt_ghost_comp u a inames pre post1)
               (mk_stt_ghost_comp u a inames pre post2) =
  let open R in
  let open RT in
  let t = R.pack_ln (R.Tv_UInst stt_ghost_fv [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (inames, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (pre, R.Q_Explicit)) in
  Rel_ctxt g post1 post2
    (Ctxt_app_arg t Q_Explicit Ctxt_hole)
    posts_equiv

let mk_total t = R.C_Total t
let mk_ghost t = R.C_GTotal t
let binder_of_t_q t q = RT.binder_of_t_q t q
let binder_of_t_q_s (t:R.term) (q:R.aqualv) (s:RT.pp_name_t) = RT.mk_binder s t q
let bound_var i : R.term = RT.bound_var i
let mk_name i : R.term = R.pack_ln (R.Tv_Var (R.pack_namedv (RT.make_namedv i)))

let arrow_dom = (R.term & R.aqualv)
let mk_arrow (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q ty q) (R.pack_comp (mk_total out)))
let mk_arrow_with_name (s:RT.pp_name_t) (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q_s ty q s) (R.pack_comp (mk_total out)))
let mk_ghost_arrow_with_name (s:RT.pp_name_t) (f:arrow_dom) (out:R.term) : R.term =
  let ty, q = f in
  R.pack_ln (R.Tv_Arrow (binder_of_t_q_s ty q s) (R.pack_comp (mk_ghost out)))
let mk_abs ty qual t : R.term = RT.mk_abs ty qual t
let mk_abs_with_name s ty qual t : R.term =  R.pack_ln (R.Tv_Abs (binder_of_t_q_s ty qual s) t)
let mk_abs_with_name_and_range s r ty qual t : R.term = 
  let b = (binder_of_t_q_s ty qual s) in
  let b = RU.binder_set_range b r in
  R.pack_ln (R.Tv_Abs b t)
  
let mk_erased (u:R.universe) (t:R.term) : R.term =
  let hd = R.pack_ln (R.Tv_UInst (R.pack_fv erased_lid) [u]) in
  R.pack_ln (R.Tv_App hd (t, R.Q_Explicit))

let mk_reveal (u:R.universe) (t:R.term) (e:R.term) : R.term =
  let hd = R.pack_ln (R.Tv_UInst (R.pack_fv reveal_lid) [u]) in
  let hd = R.pack_ln (R.Tv_App hd (t, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App hd (e, R.Q_Explicit))

let elim_exists_lid = mk_pulse_lib_core_lid "elim_exists"
let intro_exists_lid = mk_pulse_lib_core_lid "intro_exists"
let intro_exists_erased_lid = mk_pulse_lib_core_lid "intro_exists_erased"

let mk_exists (u:R.universe) (a p:R.term) =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv exists_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let mk_forall (u:R.universe) (a p:R.term) =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv forall_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let mk_elim_exists (u:R.universe) (a p:R.term) : R.term =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv elim_exists_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let mk_intro_exists (u:R.universe) (a p:R.term) (e:R.term) : R.term =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv intro_exists_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (p, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (e, R.Q_Explicit))

let mk_intro_exists_erased (u:R.universe) (a p:R.term) (e:R.term) : R.term =
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv intro_exists_erased_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (p, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (e, R.Q_Explicit))

let with_pure_lid = ["Pulse"; "Lib"; "WithPure"; "with_pure"]

let mk_with_pure (a p: R.term) =
  let t = R.pack_ln (R.Tv_FVar (R.pack_fv with_pure_lid)) in
  let t = R.pack_ln (R.Tv_App t (a, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (p, R.Q_Explicit))

let while_lid = ["Pulse"; "Lib"; "WhileLoop"; "while_loop"]

let mk_while (inv cond body:R.term) : R.term =
  let t = R.pack_ln (R.Tv_FVar (R.pack_fv while_lid)) in
  let t = R.pack_ln (R.Tv_App t (inv, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (cond, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (body, R.Q_Explicit))


let nu_while_lid = ["Pulse"; "Lib"; "WhileLoop"; "nu_while_loop"]

let mk_nu_while (inv post cond body:R.term) : R.term =
  let t = R.pack_ln (R.Tv_FVar (R.pack_fv nu_while_lid)) in
  let t = R.pack_ln (R.Tv_App t (inv, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (post, R.Q_Explicit)) in
  let t = R.pack_ln (R.Tv_App t (cond, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (body, R.Q_Explicit))

let slprop_eq_tm t1 t2 =
  let open R in
  let u2 =
    pack_universe (Uv_Succ (pack_universe (Uv_Succ (pack_universe Uv_Zero)))) in
  let t = pack_ln (Tv_UInst (pack_fv eq2_qn) [u2]) in
  let t = pack_ln (Tv_App t (pack_ln (Tv_FVar (pack_fv slprop_lid)), Q_Implicit)) in
  let t = pack_ln (Tv_App t (t1, Q_Explicit)) in
  let t = pack_ln (Tv_App t (t2, Q_Explicit)) in
  t

let non_informative_lid = mk_pulse_lib_noninformative_lid "non_informative"
let non_informative_rt (u:R.universe) (a:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (pack_fv non_informative_lid) [u]) in
  let t = pack_ln (Tv_App t (a, Q_Explicit)) in
  t

let stt_slprop_equiv_fv =
  R.pack_fv (mk_pulse_lib_core_lid "slprop_equiv")
let stt_slprop_equiv_tm =
  R.pack_ln (R.Tv_FVar stt_slprop_equiv_fv)
let stt_slprop_equiv (t1 t2:R.term) =
  let open R in
		let t = pack_ln (Tv_App stt_slprop_equiv_tm (t1, Q_Explicit)) in
		pack_ln (Tv_App t (t2, Q_Explicit))

let return_stt_lid = mk_pulse_lib_core_lid "return_stt"
let return_stt_noeq_lid = mk_pulse_lib_core_lid "return"
let return_stt_atomic_lid = mk_pulse_lib_core_lid "return_stt_atomic"
let return_stt_atomic_noeq_lid = mk_pulse_lib_core_lid "return_stt_atomic_noeq"
let return_stt_ghost_lid = mk_pulse_lib_core_lid "return_stt_ghost"
let return_stt_ghost_noeq_lid = mk_pulse_lib_core_lid "return_stt_ghost_noeq"

let mk_stt_return (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_return_noeq (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_noeq_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_atomic_return (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_atomic_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_atomic_return_noeq (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_atomic_noeq_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_ghost_return (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_ghost_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

let mk_stt_ghost_return_noeq (u:R.universe) (ty:R.term) (t:R.term) (post:R.term)
  : R.term =
  
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv return_stt_ghost_noeq_lid) [u]) in
  let t = R.pack_ln (R.Tv_App t (ty, R.Q_Implicit)) in
  let t = R.pack_ln (R.Tv_App t (t, R.Q_Explicit)) in
  R.pack_ln (R.Tv_App t (post, R.Q_Explicit))

// Wrapper.lift_stt_atomic<u> #a #pre #post e
let mk_lift_atomic_stt (u:R.universe) (a pre post e:R.term)  =
  let open R in
  let lid = mk_pulse_lib_core_lid "lift_stt_atomic" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

let mk_lift_ghost_neutral (u:R.universe) (a pre post e reveal_a:R.term) =
  let open R in
  let lid = mk_pulse_lib_core_lid "lift_ghost_neutral" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e, Q_Explicit)) in
  pack_ln (R.Tv_App t (reveal_a, Q_Explicit))

let mk_lift_neutral_ghost (u:R.universe) (a pre post e:R.term) =
  let open R in
  let lid = mk_pulse_lib_core_lid "lift_neutral_ghost" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e, Q_Explicit)) in
  t

let mk_lift_observability (u:R.universe) (a o1 o2 opened pre post e : R.term) =
  let open R in
  let lid = mk_pulse_lib_core_lid "lift_observablility" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (o1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (o2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.bind_stt<u1, u2> #a #b #pre1 #post1 #post2 e1 e2
let mk_bind_stt
  (u1 u2:R.universe)
  (ty1 ty2:R.term)
  (pre1 post1: R.term)
  (post2: R.term)
  (t1 t2:R.term) 
  : R.term
  = let bind_lid = mk_pulse_lib_core_lid "bind_stt" in
    let head = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
    R.mk_app
      (R.mk_app
        (R.mk_app
          (R.mk_app 
            (R.mk_app 
              (R.mk_app 
                (R.mk_app head
                          [(ty1, R.Q_Implicit)])
                [(ty2, R.Q_Implicit)])
              [(pre1, R.Q_Implicit)])
            [(post1, R.Q_Implicit)])
          [(post2, R.Q_Implicit)])
        [(t1, R.Q_Explicit)])
      [(t2, R.Q_Explicit)]

let mk_bind_ghost
  (u1 u2:R.universe)
  (a b opens pre1 post1 post2 e1 e2:R.term) =
  let open R in
  let bind_lid = mk_pulse_lib_core_lid "bind_ghost" in
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (b, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opens, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e1, Q_Explicit)) in
  pack_ln (R.Tv_App t (e2, Q_Explicit))

let mk_bind_atomic
  (u1 u2:R.universe)
  (a b obs1 obs2 opens pre1 post1 post2 e1 e2:R.term) =
  let open R in
  let bind_lid = mk_pulse_lib_core_lid "bind_atomic" in
  let t = R.pack_ln (R.Tv_UInst (R.pack_fv bind_lid) [u1;u2]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (b, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (obs1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (obs2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opens, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (e1, Q_Explicit)) in
  pack_ln (R.Tv_App t (e2, Q_Explicit))

// Wrapper.frame_stt<u> #ty #pre #post frame t
let mk_frame_stt
  (u:R.universe)
  (ty:R.term)
  (pre: R.term)
  (post: R.term)
  (frame: R.term)
  (t:R.term) 
  : R.term
  = let frame_lid = mk_pulse_lib_core_lid "frame_stt" in
    let frame_fv = R.pack_fv frame_lid in
    let frame_univ_inst u = R.pack_ln (R.Tv_UInst (R.pack_fv frame_lid) [u]) in
    let head = frame_univ_inst u in
    R.mk_app
      (R.mk_app
        (R.mk_app
          (R.mk_app
            (R.mk_app head [(ty, R.Q_Implicit)])
            [(pre, R.Q_Implicit)])
          [(post, R.Q_Implicit)])
        [(frame, R.Q_Explicit)])
      [(t, R.Q_Explicit)]

// Wrapper.frame_stt_atomic<u> #a #opened #pre #post frame e
let mk_frame_stt_atomic (u:R.universe) (a opened pre post frame e:R.term)  =
  let open R in
  let lid = mk_pulse_lib_core_lid "frame_atomic" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (frame, Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.frame_stt_ghost<u> #a #opened #pre #post frame e
let mk_frame_stt_ghost (u:R.universe) (a pre post frame e:R.term)  =
  let open R in
  let lid = mk_pulse_lib_core_lid "frame_ghost" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (frame, Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

// Wrapper.sub_stt<u> #ty #pre1 pre2 #post1 post2 () () e
let mk_sub_stt
  (u:R.universe)
  (ty:R.term)
  (pre1 pre2: R.term)
  (post1 post2: R.term)
  (t:R.term) 
  : R.term
  = let subsumption_lid = mk_pulse_lib_core_lid "sub_stt" in
    let subsumption_fv = R.pack_fv subsumption_lid in
    let subsumption_univ_inst u = R.pack_ln (R.Tv_UInst subsumption_fv [u]) in
    let head = subsumption_univ_inst u in
    R.mk_app
     (R.mk_app 
      (R.mk_app
        (R.mk_app
          (R.mk_app
            (R.mk_app
              (R.mk_app 
                 (R.mk_app head [(ty, R.Q_Implicit)])
                 [(pre1, R.Q_Implicit)])
              [(pre2, R.Q_Explicit)])
            [(post1, R.Q_Implicit)])
          [(post2, R.Q_Explicit)])
        [(`(), R.Q_Explicit)])
      [(`(), R.Q_Explicit)])
     [(t, R.Q_Explicit)]

// Wrapper.sub_stt_atomic<u> #a #opened #pre1 pre2 #post1 post2 () () e
let mk_sub_stt_atomic (u:R.universe) (a opened pre1 pre2 post1 post2 e:R.term)  =
  let open R in
  let lid = mk_pulse_lib_core_lid "sub_atomic" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (opened, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

let mk_sub_inv_atomic (u:R.universe) (a pre post opens1 opens2 e : R.term) : R.term =
  let open R in
  let lid = mk_pulse_lib_core_lid "sub_invs_atomic" in
  let head : R.term = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  R.mk_app head
    [(a, Q_Implicit);
     (opens1, Q_Implicit);
     (opens2, Q_Implicit);
     (pre, Q_Implicit);
     (post, Q_Implicit);
     (e, Q_Explicit)]

// Wrapper.sub_stt_ghost<u> #a #opened #pre1 pre2 #post1 post2 () () e
let mk_sub_stt_ghost (u:R.universe) (a pre1 pre2 post1 post2 e:R.term)  =
  let open R in
  let lid = mk_pulse_lib_core_lid "sub_ghost" in
  let t = pack_ln (R.Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (R.Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (pre2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (post1, Q_Implicit)) in
  let t = pack_ln (R.Tv_App t (post2, Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  let t = pack_ln (R.Tv_App t (`(), Q_Explicit)) in
  pack_ln (R.Tv_App t (e, Q_Explicit))

let mk_par (u:R.universe) (aL aR preL postL preR postR eL eR:R.term) =
  let open R in
  let lid = ["Pulse"; "Lib"; "Par"; "par_stt"] in
  let t = pack_ln (Tv_UInst (R.pack_fv lid) [u]) in
  let t = pack_ln (Tv_App t (aL, Q_Implicit)) in
  let t = pack_ln (Tv_App t (aR, Q_Implicit)) in
  let t = pack_ln (Tv_App t (preL, Q_Implicit)) in
  let t = pack_ln (Tv_App t (postL, Q_Implicit)) in
  let t = pack_ln (Tv_App t (preR, Q_Implicit)) in
  let t = pack_ln (Tv_App t (postR, Q_Implicit)) in
  let t = pack_ln (Tv_App t (eL, Q_Explicit)) in
  pack_ln (Tv_App t (eR, Q_Explicit))

let tm_rewrite_tactic_t =
  let open R in
  let fv = R.pack_fv (mk_pulse_lib_core_lid "rewrite_tactic_t") in
  pack_ln (Tv_FVar fv)

let mk_rewrite (p q:R.term) =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv (mk_pulse_lib_core_lid "rewrite"))) in
  let t = pack_ln (Tv_App t (p, Q_Explicit)) in
  let t = pack_ln (Tv_App t (q, Q_Explicit)) in
  pack_ln (Tv_App t (`(), Q_Explicit))

let mk_withlocal (ret_u:R.universe) (a init pre ret_t post body:R.term) =
  let open R in
  let lid = mk_pulse_lib_reference_lid "with_local" in
  let t = pack_ln (Tv_UInst (R.pack_fv lid) [ret_u]) in
  let t = pack_ln (Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (Tv_App t (init, Q_Explicit)) in
  let t = pack_ln (Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (Tv_App t (ret_t, Q_Implicit)) in
  let t = pack_ln (Tv_App t (post, Q_Implicit)) in
  pack_ln (Tv_App t (body, Q_Explicit))

///// Utils to derive equiv for common constructs /////
let mk_star_equiv (g:R.env) (t1 t2 t3 t4:R.term)
  (eq1:RT.equiv g t1 t3)
  (eq2:RT.equiv g t2 t4)
  : RT.equiv g (mk_star t1 t2) (mk_star t3 t4) =
  
  admit ()

let mk_stt_comp_equiv (g:R.env) (u:R.universe) (res1 pre1 post1 res2 pre2 post2:R.term)
  (res_eq: RT.equiv g res1 res2)
  (pre_eq:RT.equiv g pre1 pre2)
  (post_eq:RT.equiv g post1 post2)
  : RT.equiv g (mk_stt_comp u res1 pre1 post1)
               (mk_stt_comp u res2 pre2 post2)
  = admit ()

let mk_stt_atomic_comp_equiv (g:R.env) obs (u:R.universe) (res inames pre1 post1 pre2 post2:R.term)
  (pre_eq:RT.equiv g pre1 pre2)
  (post_eq:RT.equiv g post1 post2)
  : RT.equiv g (mk_stt_atomic_comp obs u res inames pre1 post1)
               (mk_stt_atomic_comp obs u res inames pre2 post2)
  = admit ()

let mk_stt_ghost_comp_equiv (g:R.env) (u:R.universe) (res inames pre1 post1 pre2 post2:R.term)
  (pre_eq:RT.equiv g pre1 pre2)
  (post_eq:RT.equiv g post1 post2)
  : RT.equiv g (mk_stt_ghost_comp u res inames pre1 post1)
               (mk_stt_ghost_comp u res inames pre2 post2)
  = admit ()

let ref_lid = mk_pulse_lib_reference_lid "ref"
let pts_to_lid = mk_pulse_lib_reference_lid "pts_to"

let mk_ref (a:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv ref_lid)) in
  pack_ln (Tv_App t (a, Q_Explicit))

let mk_pts_to (a:R.term) (r:R.term) (perm:R.term) (v:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv pts_to_lid)) in
  let t = pack_ln (Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (Tv_App t (r, Q_Explicit)) in
  let t = pack_ln (Tv_App t (perm, Q_Implicit)) in
  pack_ln (Tv_App t (v, Q_Explicit))

let pulse_lib_array_core = ["Pulse"; "Lib"; "Array"; "Core"]
let mk_pulse_lib_array_core_lid s = pulse_lib_array_core @ [s]

let array_lid = mk_pulse_lib_array_core_lid "array"
let array_pts_to_lid = mk_pulse_lib_array_core_lid "pts_to"
let array_length_lid = mk_pulse_lib_array_core_lid "length"
let array_is_full_lid = mk_pulse_lib_array_core_lid "is_full_array"

let mk_array (a:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv array_lid)) in
  pack_ln (Tv_App t (a, Q_Explicit))

let mk_array_length (a:R.term) (arr:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv array_length_lid)) in
  let t = pack_ln (Tv_App t (a, Q_Implicit)) in
  pack_ln (Tv_App t (arr, Q_Explicit))

let mk_array_pts_to (a:R.term) (arr:R.term) (perm:R.term) (v:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv array_pts_to_lid)) in
  let t = pack_ln (Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (Tv_App t (arr, Q_Explicit)) in
  let t = pack_ln (Tv_App t (perm, Q_Implicit)) in
  pack_ln (Tv_App t (v, Q_Explicit))

// let mk_array_is_full (a:R.term) (arr:R.term) : R.term =
//   let open R in
//   let t = pack_ln (Tv_FVar (pack_fv array_is_full_lid)) in
//   let t = pack_ln (Tv_App t (a, Q_Implicit)) in
//   pack_ln (Tv_App t (arr, Q_Explicit))

let mk_seq (u:R.universe) (a:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (R.pack_fv seq_lid) [u]) in
  pack_ln (Tv_App t (a, Q_Explicit))

let mk_seq_create (u:R.universe) (a:R.term) (len:R.term) (v:R.term) : R.term =
  let open R in
  let t = pack_ln (Tv_UInst (R.pack_fv seq_create_lid) [u]) in
  let t = pack_ln (Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (Tv_App t (len, Q_Explicit)) in
  pack_ln (Tv_App t (v, Q_Explicit))

let mk_withlocalarray (ret_u:R.universe) (a init len pre ret_t post body:R.term) =
  let open R in
  let lid = mk_pulse_lib_array_core_lid "with_local" in
  let t = pack_ln (Tv_UInst (R.pack_fv lid) [ret_u]) in
  let t = pack_ln (Tv_App t (a, Q_Implicit)) in
  let t = pack_ln (Tv_App t (init, Q_Explicit)) in
  let t = pack_ln (Tv_App t (len, Q_Explicit)) in
  let t = pack_ln (Tv_App t (pre, Q_Implicit)) in
  let t = pack_ln (Tv_App t (ret_t, Q_Implicit)) in
  let t = pack_ln (Tv_App t (post, Q_Implicit)) in
  pack_ln (Tv_App t (body, Q_Explicit))

let mk_szv (n:R.term) =
  let open R in
  let t = pack_ln (Tv_FVar (pack_fv szv_lid)) in
  pack_ln (Tv_App t (n, Q_Explicit))

let mk_opaque_let (g:R.env) (cur_module:R.name) (nm:string) (us: list R.univ_name) (tm:Ghost.erased R.term) (ty:R.typ{RT.typing g tm (T.E_Total, ty)})
  : T.Tac (RT.sigelt_for g (Some ty)) =
  let fv = R.pack_fv (cur_module @ [nm]) in
  let lb = R.pack_lb ({ lb_fv = fv; lb_us = us; lb_typ = ty; lb_def = (`_) }) in
  let se = R.pack_sigelt (R.Sg_Let false [lb]) in
  let pf : RT.sigelt_typing g se =
    RT.ST_Let_Opaque g fv us ty ()
  in
  (true, se, None)

let mk_observability_lid l = ["PulseCore"; "Observability"; l]
let observable_lid = mk_observability_lid "Observable"
let neutral_lid = mk_observability_lid "Neutral"

let later_lid = mk_pulse_lib_core_lid "later"
let iname_lid = mk_pulse_lib_core_lid "iname"
let inames_lid = mk_pulse_lib_core_lid "inames"
let inv_lid = mk_pulse_lib_core_lid "inv"
let emp_inames_lid = mk_pulse_lib_core_lid "emp_inames"
let all_inames_lid = mk_pulse_lib_core_lid "all_inames"
let add_inv_lid = mk_pulse_lib_core_lid "add_inv"
let remove_inv_lid = mk_pulse_lib_core_lid "remove_inv"

let remove_inv_tm (is iname:R.term) : R.term =
  let h = R.pack_ln (R.Tv_FVar (R.pack_fv remove_inv_lid)) in
  R.mk_app h [ex is; ex iname]
let mk_mem_inv (is iname:R.term) : R.term =
  let mem_inv_tm = mk_pulse_lib_core_lid "mem_inv" in
  let t = R.pack_ln (R.Tv_FVar (R.pack_fv mem_inv_tm)) in
  R.mk_app t [ ex is; ex iname ]

let inv_disjointness_goal (is iname:R.term) : R.term =
  let p = mk_mem_inv is iname in
  let u0 = R.pack_universe R.Uv_Zero in
  let p = mk_reveal u0 bool_tm p in
  mk_eq2 u0 bool_tm (`false) p

let fv_has_attr_string (attr_name:string) (f : R.fv) : T.Tac bool =
  match T.lookup_typ (T.top_env ()) (T.inspect_fv f) with
  | None -> false
  | Some se ->
    let attrs = T.sigelt_attrs se in
    attrs |> T.tryFind (fun a -> T.is_fvar a attr_name)

let head_has_attr_string (attr_name:string) (t : R.term) : T.Tac bool =
  match T.hua t with
  | None -> false
  | Some (hfv, _, _) ->
    fv_has_attr_string attr_name hfv

let rec eq_list (f:'a -> 'a -> bool) (l1 l2:list 'a) : bool =
  match l1, l2 with
  | [], [] -> true
  | x1::xs1, x2::xs2 -> f x1 x2 && eq_list f xs1 xs2
  | _ -> false

let eq_ident (i1 i2:R.ident) : bool =
  R.compare_ident i1 i2 = Order.Eq

let qual_eq (q1 q2:R.qualifier) : bool =
  let open R in
  match q1, q2 with
  | Assumption, Assumption
  | InternalAssumption, InternalAssumption
  | New, New
  | Private, Private
  | Unfold_for_unification_and_vcgen, Unfold_for_unification_and_vcgen
  | Visible_default, Visible_default
  | Irreducible, Irreducible
  | Inline_for_extraction, Inline_for_extraction
  | NoExtract, NoExtract
  | Noeq, Noeq
  | Unopteq, Unopteq
  | TotalEffect, TotalEffect
  | Logic, Logic
  | Reifiable, Reifiable -> true
  | Reflectable n1, Reflectable n2
  | Discriminator n1, Discriminator n2 
  | Action n1, Action n2 -> n1 = n2 
  | Projector (n1, i1), Projector (n2, i2) ->
    n1 = n2 && eq_ident i1 i2
  | RecordType (ids1, ids1'), RecordType (ids2, ids2')
  | RecordConstructor (ids1, ids1'), RecordConstructor (ids2, ids2') ->
    eq_list eq_ident ids1 ids2 &&
    eq_list eq_ident ids1' ids2'
  | ExceptionConstructor, ExceptionConstructor
  | HasMaskedEffect, HasMaskedEffect
  | Effect, Effect
  | OnlyName, OnlyName -> true
  | _ -> false

let fv_has_qual (qual:R.qualifier) (f : R.fv) : T.Tac bool =
  match T.lookup_typ (T.top_env ()) (T.inspect_fv f) with
  | None -> false
  | Some se ->
    let quals = T.sigelt_quals se in
    quals |> T.tryFind (fun x -> qual_eq qual x)