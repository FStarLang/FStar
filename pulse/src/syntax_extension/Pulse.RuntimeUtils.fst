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

module Pulse.RuntimeUtils

(* The interface is written against the user-facing reflection API (it is
   used by the checker), while this implementation calls the compiler
   directly.  The two sets of types are the same at runtime (the FStar.Stubs
   modules are the compiler's, see doc/ref/custard.md, section 8.2), but
   distinct in F*, so this module converts between them with [co].
   Likewise, the effects of the interface (Tot, Dv, Tac) are those the
   checker needs, while the compiler's functions are all in ML. *)

open FStar.Tactics.V2
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2

open FStarC
open FStarC.Effect
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module TcEnv = FStarC.TypeChecker.Env
module Rel = FStarC.TypeChecker.Rel
module Free = FStarC.Syntax.Free
module FlatSet = FStarC.FlatSet
module Range = FStarC.Range
module E = FStarC.Errors
module Basic = FStarC.Tactics.V2.Basic
module TM = FStarC.Tactics.Monad
module WeakMemo = Pulse.RuntimeUtils.WeakMemo
open Pulse.RuntimeUtils.Types

(* This unit is checked with --lax, so the equality proof is trivial. *)
let co (#a #b : Type) (x:a) : b = FStar.Pervasives.coerce_eq #a #b () x

(* FStar.Range.range is the compiler's range at runtime (src/basic/FStar.Range.fst),
   but abstract here. *)
let rr (r:range) : Range.range = co r
let ur (r:Range.range) : range = co r

(* Run an ML computation at another effect.  Every function of this
   module is impure in the compiler's sense, as is everything in the
   compiler; the interface only claims what the checker needs. *)
let ml_tot (#a:Type) (f:unit -> ML a) : a = (co f <: unit -> Tot a) ()
let ml_dv (#a:Type) (f:unit -> ML a) : Dv a = (co f <: unit -> Dv a) ()

(* A user tactic is the compiler's [tac]: both are functions of the proof
   state (doc/ref/custard.md, section 7.5).  TAC is not reifiable, so a
   tactic thunk is run by coercing it. *)
let tac (a:Type) = FStarC.Tactics.Types.ref_proofstate -> ML a
let mk_tac (#a:Type) (t:tac a) : T.Tac a = T.TAC?.reflect (co t)
let run_tac (#a:Type) (f:unit -> T.Tac a) : tac a = (co f <: unit -> tac a) ()

type ctx_elt = string & option Range.range

let ctxt_elt_as_string (sr : ctx_elt) : ML string =
  let s, r = sr in
  match r with
  | None -> s
  | Some r -> "@" ^ Range.string_of_range r ^ ": " ^ s

let extend_context (tag:string) (r:option range) (ctx:context) : context =
  co ((tag, (co r <: option Range.range)) :: (co ctx <: list ctx_elt))

(* The rendered strings of a context, memoized per context.  Contexts are
   immutable lists extended by consing (extend_context), and the same (often
   very long) context is passed to with_context on every call into the F*
   typechecker, so rendering every element on every call would be quadratic
   overall.  The memo table has weak keys, so that dead contexts can be
   collected; the cached strings are exactly those computed by
   ctxt_elt_as_string. *)
#push-options "--warn_error -272" //intentional top-level effect
let ctx_memo : (list ctx_elt -> ML (option (list string))) & (list ctx_elt -> list string -> ML unit) =
  WeakMemo.create ()
#pop-options

let rec context_strings (c:list ctx_elt) : ML (list string) =
  match c with
  | [] -> []
  | sr::tl ->
    match fst ctx_memo c with
    | Some ss -> ss
    | None ->
      let ss = ctxt_elt_as_string sr :: context_strings tl in
      snd ctx_memo c ss;
      ss

let with_context (c:context) (f:unit -> T.Tac 'a) : T.Tac 'a =
  mk_tac (fun ps ->
    E.with_ctxs (context_strings (co c)) (fun _ -> run_tac f ps))

let with_error_bound (r:range) (f:unit -> T.Tac 'a) : T.Tac 'a =
  mk_tac (fun ps -> E.with_error_bound (rr r) (fun _ -> run_tac f ps))

exception Quiet_failure

let try_quietly (#a:Type) (f:unit -> T.Tac a) : T.Tac (option a) =
  mk_tac (fun ps ->
    (* TM.catch is at Type0, so the result goes through a dyn. *)
    let attempt : TM.tac FStar.Dyn.dyn = fun ps ->
      let errs, rest, r = E.catch_errors_aux (fun () -> run_tac f ps) in
      match errs, r with
      | [], Some x -> E.add_issues rest; FStar.Dyn.mkdyn x
      | _ -> raise Quiet_failure
    in
    match TM.catch attempt ps with
    | Inr x -> Some (FStar.Dyn.undyn x)
    | Inl _ -> None)

let get_error_bound () : T.Tac (option range) =
  mk_tac (fun _ -> co !E.error_range_bound)

let with_extv (k v : string) (f:unit -> T.Tac 'a) : T.Tac 'a =
  mk_tac (fun ps ->
    let x = Options.Ext.save () in
    Options.Ext.set k v;
    let res = run_tac f ps in
    Options.Ext.restore x;
    res)

let print_context (c:context) : T.Tac string =
  mk_tac (fun _ ->
    String.concat "\n>" (List.map ctxt_elt_as_string (co c <: list ctx_elt)))

let debug_at_level_no_module (s:string) : bool =
  ml_tot (fun () -> !(Debug.get_toggle s))

let debug_at_level (g:env) (s:string) : bool =
  debug_at_level_no_module s

let print_exn (e:exn) : string =
  ml_tot (fun () ->
    match e with
    | FStarC.Tactics.Common.TacticFailure (s, _) ->
      "TacticFailure " ^ FStarC.Errors.Msg.rendermsg s
    | _ -> Util.print_exn e)

let next_id () : Dv nat = ml_dv (fun () -> co (GenSym.next_id ()))

let binder_set_range (x:R.binder) (r:range) : b:R.binder{b==x} =
  ml_tot (fun () ->
    let b : S.binder = co x in
    co { b with S.binder_bv = S.set_range_of_bv b.binder_bv (rr r) })

let binder_range (x:R.binder) : range =
  ur (S.range_of_bv (co x <: S.binder).binder_bv)

let range_of_term (t:T.term) : range = ur (co t <: S.term).pos

let start_of_range (r:range) : range =
  let r = rr r in
  ur (Range.mk_range (Range.file_of_range r) (Range.start_of_range r) (Range.start_of_range r))

let set_range (t:T.term) (r:range) : t':T.term{t == t'} =
  co { (co t <: S.term) with S.pos = rr r }

let set_use_range (t:T.term) (r:range) : t':T.term{t == t'} =
  ml_tot (fun () -> co (FStarC.Syntax.Subst.set_use_range (rr r) (co t)))

let error_code_uninstantiated_variable () : int =
  ml_tot (fun () -> E.errno FStarC.Errors.Codes.Error_UninstantiatedUnificationVarInTactic)

let is_range_zero (r:range) : Dv bool =
  let r = rr r in
  Range.compare r Range.dummyRange = 0 &&
  Range.compare_use_range r Range.dummyRange = 0

let union_ranges (r0 r1:range) : range =
  ml_tot (fun () -> ur (Range.union_ranges (rr r0) (rr r1)))

let env_get_range (g:env) : range = ur (TcEnv.get_range (co g))

let env_set_range (g:env) (r:range) : g':env{g==g'} =
  co (TcEnv.set_range (co g) (rr r))

let env_set_context (g:env) (ctx:context) : g':env{g==g'} = g

(* The compiler's lazy embeddings are at Type0, so the payloads go through a
   dyn. *)
let embed_st_term_for_extraction (#a:Type) (d:a) (r:option range) : T.term =
  ml_tot (fun () ->
    co (U.mk_lazy (FStar.Dyn.mkdyn d) S.tun (S.Lazy_extension "pulse_st_term") (co r)))

let unembed_st_term_for_extraction (#a:Type0) (d:T.term) : a =
  ml_tot (fun () ->
    let x : FStar.Dyn.dyn = U.unlazy_as_t (S.Lazy_extension "pulse_st_term") (co d) in
    FStar.Dyn.undyn (co x))

let unembed_pulse_decl (#a:Type) (#b:Type0) (d:a) : b =
  let d : S.term = co (FStar.Dyn.mkdyn d) in
  ml_tot (fun () ->
    let x : FStar.Dyn.dyn = U.unlazy_as_t (S.Lazy_extension "pulse_decl") d in
    FStar.Dyn.undyn (co x))

let push_univ_vars (g:env) (us:list R.univ_name) : g':env { g' == g } =
  ml_tot (fun () -> co (TcEnv.push_univ_vars (co g) (co us)))

let debug_subst (s:list R.subst_elt) (t:T.term) (r1 r2:T.term) : y:T.term{ y == r1 } =
  if ml_tot (fun () -> Options.Ext.get "pulse:subst" <> "")
  then co r2
  else r1

let deep_compress (t:T.term) : r:T.term { t == r } =
  ml_tot (fun () -> co (FStarC.Syntax.Compress.deep_compress_uvars (co t)))

let deep_compress_safe (t:T.term) : r:T.term { t == r } =
  ml_tot (fun () -> co (FStarC.Syntax.Compress.deep_compress true true (co t)))

let no_uvars_in_term (t:T.term) : Dv bool =
  ml_dv (fun () -> Basic.no_uvars_in_term (co t))

(* Tm_app is unary in FStarC.Syntax.Syntax, so every application is already
   in unary form and there is nothing to do here. *)
let deep_transform_to_unary_applications (t:T.term) : r:T.term { t == r } = t

let map_seal_nd (s:FStar.Sealed.sealed 't) (f:'t -> 'u) () : Nd (FStar.Sealed.sealed 'u) =
  FStar.Sealed.seal (f (FStar.Sealed.unseal s))
let map_seal (s:FStar.Sealed.sealed 't) (f:'t -> 'u) : FStar.Sealed.sealed 'u =
  co #(unit -> Nd (FStar.Sealed.sealed 'u)) #(unit -> Tot (FStar.Sealed.sealed 'u))
    (map_seal_nd s f) ()

let float_one : FStar.Float64.float64 = FStar.Float64.one

let lax_check_term_with_unknown_universes (g:env) (t:T.term) : Dv (option T.term) =
  ml_dv (fun () ->
    let g : TcEnv.env = co g in
    let e : S.term = co t in
    let issues, res =
      E.catch_errors (fun _ ->
        if Basic.no_uvars_in_g g && Basic.no_uvars_in_term e
        then (
          match e.n with
          | S.Tm_fvar { fv_qual = Some q }
              when not (S.Unresolved_name? q) ->
            (* record projectors etc. are pure *)
            None
          | _ ->
            let g = TcEnv.set_range g e.pos in
            let must_tot = false in
            let g = { g with TcEnv.instantiate_imp = false; phase1 = true; admit = true } in
            let e, t, guard = g.typeof_tot_or_gtot_term g e must_tot in
            let _ = Rel.resolve_implicits g guard in
            let uvs = FlatSet.union (Free.uvars e) (Free.uvars t) in
            if not (FlatSet.is_empty uvs)
            then None
            else (
              let univs = FlatSet.union (Free.univs e) (Free.univs t) in
              List.iter (fun univ -> FStarC.Syntax.Unionfind.univ_change univ S.U_unknown)
                (FlatSet.elems univs);
              Some (FStarC.Syntax.Compress.deep_compress false true t)
            )
        )
        else None)
    in
    E.add_issues issues;
    match res with
    | Some (Some x) -> Some (co x)
    | _ -> None)

let phase1 (g:env) : TcEnv.env =
  { (co g <: TcEnv.env) with TcEnv.phase1 = true; admit = true }

let new_implicit_var (reason:string) (r:range) (g:env) (e:typ) (unrefine:bool) : Dv term =
  ml_dv (fun () ->
    let uvar, _, _ = FStarC.TypeChecker.Util.new_implicit_var reason (rr r) (phase1 g) (co e) unrefine in
    co uvar)

let try_solve_single_valued_implicits (g:env) (ts:list term) : Dv unit =
  ml_dv (fun () ->
    let imps = List.filter_map (fun (t:T.term) ->
      let t = FStarC.Syntax.Subst.compress (co t) in
      match t.n with
      | S.Tm_uvar (ctx_u, _) ->
        Some { FStarC.TypeChecker.Common.imp_reason = "single-valued implicit";
               imp_uvar = ctx_u;
               imp_tm = t;
               imp_range = t.pos }
      | _ -> None) ts
    in
    ignore (Rel.try_solve_single_valued_implicits (phase1 g) false imps))

let tc_term_phase1 (g:env) (t:T.term) (instantiate_imps:bool)
  : Dv (option (T.term & T.term & T.tot_or_ghost) & T.issues) =
  ml_dv (fun () ->
    let e : S.term = co t in
    let issues, res = E.catch_errors (fun _ ->
      let g = TcEnv.set_range (co g) e.pos in
      let g = { g with TcEnv.phase1 = true; admit = true; instantiate_imp = instantiate_imps } in
      let e, c, guard = FStarC.TypeChecker.TcTerm.tc_tot_or_gtot_term g e in
      let t = U.comp_result c in
      let c = FStarC.TypeChecker.Normalize.maybe_ghost_to_pure g c in
      let eff =
        if U.is_total_comp c
        then FStarC.TypeChecker.Core.E_Total
        else FStarC.TypeChecker.Core.E_Ghost in
      let guard = Rel.solve_deferred_constraints g guard in
      let _ = Rel.resolve_implicits g guard in
      e, t, eff)
    in
    co res, co issues)

let teq_nosmt_force (g:env) (ty1 ty2:T.term) : Dv bool =
  ml_dv (fun () ->
    let ty1 : S.term = co ty1 in
    let _, res = E.catch_errors (fun _ ->
      Rel.teq_nosmt_force (TcEnv.set_range (co g) ty1.pos) ty1 (co ty2)) in
    match res with
    | Some true -> true
    | _ -> false)

let teq_nosmt_force_phase1 (g:env) (ty1 ty2:T.term) : Dv bool =
  teq_nosmt_force (co (phase1 g)) ty1 ty2

let teq_nosmt_phase1 (g:env) (ty1 ty2:T.term) : Dv bool =
  ml_dv (fun () ->
    let ty1 : S.term = co ty1 in
    let _, res = E.catch_errors (fun _ ->
      Rel.teq_nosmt (TcEnv.set_range (phase1 g) ty1.pos) ty1 (co ty2)) in
    match res with
    | Some (Some _) -> true
    | _ -> false)

let whnf_lax (g:env) (t:T.term) : T.term =
  ml_tot (fun () ->
    co (FStarC.TypeChecker.Normalize.unfold_whnf' [TcEnv.Unascribe] (co g) (co t)))

let hnf_lax (g:env) (t:T.term) : T.term =
  ml_tot (fun () ->
    co (FStarC.TypeChecker.Normalize.normalize
          [TcEnv.Unascribe; TcEnv.Primops; TcEnv.HNF; TcEnv.UnfoldUntil S.delta_constant; TcEnv.Beta]
          (co g) (co t)))

let beta_lax (g:env) (t:T.term) : T.term =
  ml_tot (fun () ->
    co (FStarC.TypeChecker.Normalize.normalize [TcEnv.Unascribe; TcEnv.Beta] (co g) (co t)))

let norm_well_typed_term #g #t #eff #k _ steps =
  mk_tac (fun _ ->
    let steps = Pulse.RuntimeUtils.NormSteps.translate_norm_steps steps in
    let t' : S.term =
      FStarC.TypeChecker.Normalize.normalize (TcEnv.Unascribe :: steps) (co g) (co t) in
    co (Mkdtuple3 #S.term #(fun _ -> unit) #(fun _ _ -> unit) t' () ()))

let add_attribute (x:T.sigelt) (a:R.term) : (y:T.sigelt { x == y }) =
  ml_tot (fun () ->
    let s : S.sigelt = co x in
    co { s with S.sigattrs = co a :: s.sigattrs })

let get_attributes (x:T.sigelt) : T.Tac (list R.term) =
  mk_tac (fun _ -> co (co x <: S.sigelt).sigattrs)

let add_noextract_qual (x:T.sigelt) : (y:T.sigelt { x == y }) =
  ml_tot (fun () ->
    let s : S.sigelt = co x in
    co { s with S.sigquals = S.NoExtract :: s.sigquals })

let must_erase_for_extraction (g:env) (ty:T.term) : bool =
  ml_tot (fun () -> FStarC.TypeChecker.Util.must_erase_for_extraction (co g) (co ty))

let magic #a () = admit ()

let magic_s #a (s:string) : a =
  let () = ml_tot (fun () -> failwith ("Cannot execute magic: " ^ s) <: unit) in
  admit ()

let profile (f:unit -> T.Tac 'b) (module_name:name) (component_name:string) : T.Tac 'b =
  mk_tac (fun ps ->
    FStarC.Profiling.profile (fun () -> run_tac f ps)
      (Some (String.concat "." module_name)) component_name)

let mk_app_flat (head:T.term) (args:list T.argv) (r:range) : T.term =
  ml_tot (fun () ->
    let args = List.map (fun (x, q) -> co x, FStarC.Reflection.V2.Builtins.pack_aqual (co q)) args in
    co (S.mk_Tm_app (co head) args (rr r)))

let record_stats (key:string) (f:unit -> T.Tac 'a) : T.Tac 'a =
  mk_tac (fun ps -> FStarC.Stats.record key (fun () -> run_tac f ps))

let stack_dump () : Dv string = ml_dv Util.stack_dump

let push_options () : Dv unit = ml_dv Options.push
let pop_options () : Dv unit = ml_dv Options.pop
let set_options (opts:string) : Dv unit =
  ml_dv (fun () -> ignore (Options.set_options opts))

let universe_of_well_typed_term g t =
  mk_tac (fun _ ->
    try Some (co (FStarC.TypeChecker.TcTerm.universe_of (co g) (co t)))
    with | _ -> None)

let try_lookup_lid (g:T.env) (lid:R.name) : option ((universes & typ) & range) =
  ml_tot (fun () ->
    co (TcEnv.try_lookup_lid (co g) (Ident.lid_of_path lid Range.dummyRange)))
