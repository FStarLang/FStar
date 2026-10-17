(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStarC.Tactics.V2.Builtins

(* The implementation of the metaprogramming primitives of
   ulib/FStar.Stubs.Tactics.V2.Builtins.fsti for compiled metaprograms
   (plugins).  Custard resolves a reference to FStar.Stubs.Tactics.V2.Builtins.f
   to FStarC.Tactics.V2.Builtins.f (see Extract.unstub_lid).

   A [Tac a] computation is represented as a function from the proofstate
   reference, which is exactly the compiler's [tac a]; so most primitives are
   simply the compiler's implementation.  A [unit -> Tac a] argument is
   applied to [()] to obtain the compiler's [tac a]. *)

open FStarC
open FStarC.Effect
open FStarC.Tactics.Types
open FStarC.Tactics.Monad

module B    = FStarC.Tactics.V2.Basic
module TM   = FStarC.Tactics.Monad
module CTRW = FStarC.Tactics.CtrlRewrite
module S    = FStarC.Syntax.Syntax

let get () : ML (tac proofstate) = TM.get

let unquote (#a:Type) (t:S.term) : ML (tac a) =
  failwith "Sorry, unquote does not work in compiled tactics"

let catch (t : unit -> ML (tac 'a)) : ML (tac (either exn 'a)) =
  TM.catch (t ())

let raise_core (e:exn) : tac unit = TM.traise e

let with_compat_pre_core (n:int) (f : unit -> ML (tac 'a)) : ML (tac 'a) =
  B.with_compat_pre_core n (f ())

let ctrl_rewrite (d:direction)
                 (t1 : S.term -> ML (tac (bool & ctrl_flag)))
                 (t2 : unit -> ML (tac unit))
  : ML (tac unit)
  = CTRW.ctrl_rewrite d t1 (t2 ())

let call_subtac g (t : unit -> ML (tac unit)) u ty =
  B.call_subtac g (t ()) u ty

let stats_record (s:string) (f : unit -> ML (tac 'c)) : ML (tac 'c) =
  B.stats_record () () s (f ())

let with_error_context (s:string) (f : unit -> ML (tac 'c)) : ML (tac 'c) =
  B.with_error_context () () s (f ())

let fresh_universe_uvar x1 = B.fresh_universe_uvar x1

let fixup_range x1 = B.fixup_range x1
let compress x1 = B.compress x1
let compress_univ x1 = B.compress_univ x1
let set_goals x1 = TM.set_goals x1
let set_smt_goals x1 = TM.set_smt_goals x1
let top_env x1 = B.top_env x1
let fresh x1 = B.fresh x1
let refine_intro x1 = B.refine_intro x1
let tc x1 x2 = B.tc x1 x2
let tcc x1 x2 = B.tcc x1 x2
let unshelve x1 = B.unshelve x1
let norm x1 = B.norm x1
let norm_term_env x1 x2 x3 = B.norm_term_env x1 x2 x3
let norm_binding_type x1 x2 = B.norm_binding_type x1 x2
let intro x1 = B.intro x1
let intros x1 = B.intros x1
let intro_rec x1 = B.intro_rec x1
let rename_to x1 x2 = B.rename_to x1 x2
let revert x1 = B.revert x1
let var_retype x1 = B.var_retype x1
let clear_top x1 = B.clear_top x1
let clear x1 = B.clear x1
let rewrite x1 = B.rewrite x1
let grewrite x1 x2 = B.grewrite x1 x2
let t_exact x1 x2 x3 = B.t_exact x1 x2 x3
let t_apply x1 x2 x3 x4 = B.t_apply x1 x2 x3 x4
let t_apply_lemma x1 x2 x3 = B.t_apply_lemma x1 x2 x3
let print x1 = B.print x1
let debugging x1 = B.debugging x1
let ide x1 = B.ide x1
let dump x1 = B.dump x1
let dump_all x1 x2 = B.dump_all x1 x2
let dump_uvars_of x1 x2 = B.dump_uvars_of x1 x2
let t_trefl x1 = B.t_trefl x1
let dup x1 = B.dup x1
let prune x1 = B.prune x1
let addns x1 = B.addns x1
let t_destruct x1 = B.t_destruct x1
let set_options x1 = B.set_options x1
let uvar_env x1 x2 = B.uvar_env x1 x2
let ghost_uvar_env x1 x2 = B.ghost_uvar_env x1 x2
let unify_env x1 x2 x3 = B.unify_env x1 x2 x3
let unify_guard_env x1 x2 x3 = B.unify_guard_env x1 x2 x3
let match_env x1 x2 x3 = B.match_env x1 x2 x3
let launch_process x1 x2 x3 = B.launch_process x1 x2 x3
let fresh_bv_named x1 = B.fresh_bv_named x1
let change x1 = B.change x1
let get_guard_policy x1 = B.get_guard_policy x1
let set_guard_policy x1 = B.set_guard_policy x1
let lax_on x1 = B.lax_on x1
let tadmit_t x1 = B.tadmit_t x1
let join x1 = B.join x1
let curms x1 = B.curms x1
let set_urgency x1 = B.set_urgency x1
let set_dump_on_failure x1 = B.set_dump_on_failure x1
let t_commute_applied_match x1 = B.t_commute_applied_match x1
let gather_or_solve_explicit_guards_for_resolved_goals x1 = B.gather_explicit_guards_for_resolved_goals x1
let string_to_term x1 x2 = B.string_to_term x1 x2
let push_bv_dsenv x1 x2 = B.push_bv_dsenv x1 x2
let term_to_string x1 = B.term_to_string x1
let comp_to_string x1 = B.comp_to_string x1
let term_to_doc x1 = B.term_to_doc x1
let comp_to_doc x1 = B.comp_to_doc x1
let range_to_string x1 = B.range_to_string x1
let get_vconfig x1 = B.get_vconfig x1
let set_vconfig x1 = B.set_vconfig x1
let t_smt_sync x1 = B.t_smt_sync x1
let free_uvars x1 = B.free_uvars x1
let all_ext_options x1 = B.all_ext_options x1
let ext_getv x1 = B.ext_getv x1
let ext_enabled x1 = B.ext_enabled x1
let ext_getns x1 = B.ext_getns x1
let alloc x1 = B.alloc x1
let read x1 = B.read x1
let write x1 x2 = B.write x1 x2
let splice_quals x1 = B.splice_quals x1
let splice_attrs x1 = B.splice_attrs x1
let is_non_informative x1 x2 = B.refl_is_non_informative x1 x2
let check_subtyping x1 x2 x3 = B.refl_check_subtyping x1 x2 x3
let t_check_equiv x1 x2 x3 x4 x5 = B.t_refl_check_equiv x1 x2 x3 x4 x5
let core_compute_term_type x1 x2 = B.refl_core_compute_term_type x1 x2
let core_check_term x1 x2 x3 x4 = B.refl_core_check_term x1 x2 x3 x4
let core_check_term_at_type x1 x2 x3 = B.refl_core_check_term_at_type x1 x2 x3
let check_match_complete x1 x2 x3 x4 = B.refl_check_match_complete x1 x2 x3 x4
let tc_term x1 x2 = B.refl_tc_term x1 x2
let universe_of x1 x2 = B.refl_universe_of x1 x2
let check_prop_validity x1 x2 = B.refl_check_prop_validity x1 x2
let instantiate_implicits x1 x2 x3 x4 = B.refl_instantiate_implicits x1 x2 x3 x4
let try_unify x1 x2 x3 x4 = B.refl_try_unify x1 x2 x3 x4
let maybe_relate_after_unfolding x1 x2 x3 = B.refl_maybe_relate_after_unfolding x1 x2 x3
let maybe_unfold_head x1 x2 = B.refl_maybe_unfold_head x1 x2
let norm_well_typed_term x1 x2 x3 = B.refl_norm_well_typed_term x1 x2 x3
let push_open_namespace x1 x2 = B.push_open_namespace x1 x2
let push_module_abbrev x1 x2 x3 = B.push_module_abbrev x1 x2 x3
let resolve_name x1 x2 = B.resolve_name x1 x2
let log_issues x1 = B.log_issues x1
let call_subtac_tm x1 x2 x3 x4 = B.call_subtac_tm x1 x2 x3 x4
