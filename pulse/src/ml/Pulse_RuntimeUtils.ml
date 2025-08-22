open Fstarcompiler
type context = ((string * FStarC_Range.range option) list) (* FStar_Sealed.sealed *)
let extend_context (s:string) (r:FStarC_Range.range option) (c:context) = (s,r)::c
module TR = FStarC_Tactics_Result

type ('a,'wp) tac_repr = FStarC_Tactics_Types.proofstate -> 'a TR.__result
type 'a utac = ('a, unit) tac_repr 

let ctxt_elt_as_string (s, r) =
    match r with
    | None -> s
    | Some r ->
      "@" ^ FStarC_Range.string_of_range r ^ ": " ^ s
let rec print_context (c:context) : string utac =
  fun ps ->
    TR.Success (
      String.concat "\n>" (List.map ctxt_elt_as_string c),
      ps
    )
let rec with_context (c:context) (f: unit -> 'a utac) : 'a utac =
  fun ps ->
    match c with
    | [] -> f () ps
    | sr::tl ->
      with_context tl (fun _ ps ->
      FStarC_Errors.with_ctx (ctxt_elt_as_string sr) (fun _ -> f () ps)) ps
let with_error_bound (r:FStarC_Range.range) (f: unit -> 'a utac) : 'a utac =
  fun ps ->
    FStarC_Errors.with_error_bound r (fun _ -> f () ps)
let with_extv (k:string) (v:string) (f: unit -> 'a utac) : 'a utac =
  fun ps ->
    let open FStarC_Options_Ext in
    let x = FStarC_Options_Ext.save() in
    FStarC_Options_Ext.set k v;
    let res = f () ps in
    FStarC_Options_Ext.restore x;
    res
let env_set_context (g:FStarC_Reflection_Types.env) (c:context) = g
let print_exn (e:exn) = Printexc.to_string e
let debug_at_level_no_module (s:string) =
  let r = FStarC_Debug.get_toggle s in
  !r
let debug_at_level (g:FStarC_Reflection_Types.env) (s:string) =
  let r = FStarC_Debug.get_toggle s in
  !r

let next_id () = FStarC_GenSym.next_id ()
let bv_set_range (bv:FStarC_Syntax_Syntax.bv) (r:FStarC_Range.range) = FStarC_Syntax_Syntax.set_range_of_bv bv r
let bv_range (bv:FStarC_Syntax_Syntax.bv) = FStarC_Syntax_Syntax.range_of_bv bv
let binder_set_range (b:FStarC_Syntax_Syntax.binder) (r:FStarC_Range.range) =
    { b with FStarC_Syntax_Syntax.binder_bv = (bv_set_range b.FStarC_Syntax_Syntax.binder_bv r) }
let binder_range (b:FStarC_Syntax_Syntax.binder) = bv_range b.FStarC_Syntax_Syntax.binder_bv
let start_of_range (r:FStarC_Range.range) =
  let open FStarC_Range in
  mk_range (file_of_range r) (start_of_range r) (start_of_range r)
  let set_range (t:FStarC_Syntax_Syntax.term) (r:FStarC_Range.range) = { t with FStarC_Syntax_Syntax.pos = r}
let set_use_range (t:FStarC_Syntax_Syntax.term) (r:FStarC_Range.range) = FStarC_Syntax_Subst.set_use_range r t
let error_code_uninstantiated_variable () = FStarC_Errors.errno FStarC_Errors_Codes.Error_UninstantiatedUnificationVarInTactic
let is_range_zero (r:FStarC_Range.range) = r = FStarC_Range.dummyRange
let union_ranges (r0:FStarC_Range.range) (r1:FStarC_Range.range) = FStarC_Range.union_ranges r0 r1
let range_of_term (t:FStarC_Syntax_Syntax.term) = t.FStarC_Syntax_Syntax.pos
let env_set_range (e:FStarC_Reflection_Types.env) (r:FStarC_Range.range) =
   FStarC_TypeChecker_Env.set_range e r

let is_pulse_option_set (x:string) : bool =
  let key = ("pulse:"^x) in
  let value = FStarC_Options_Ext.get key in
  value <> ""

module U = FStarC_Syntax_Util
module S = FStarC_Syntax_Syntax
let embed_st_term_for_extraction (d:'a) r =
   U.mk_lazy d S.tun (S.Lazy_extension "pulse_st_term") r
let unembed_st_term_for_extraction (d:S.term) : 'a =
   U.unlazy_as_t (S.Lazy_extension "pulse_st_term") d
let unembed_pulse_decl (d:'a) : 'b =
   U.unlazy_as_t (S.Lazy_extension "pulse_decl") (Obj.magic d)

let push_univ_vars g us =
  FStarC_TypeChecker_Env.push_univ_vars g us

let debug_subst (s:S.subst_elt list) (t:S.term) (r1:S.term) (r2:S.term) =
  if is_pulse_option_set "subst"
  then r2
  else r1
  (*
  FStarC_Options.debug_at_level_no_module
  let open FStarC_Util in
  if U.term_eq_dbg true r1 r2
  then r1
  else (
    print4 "Applied subst %s to %s\nExpected %s\nGot %s\n"
        (FStarC_Syntax_Print.subst_to_string s)
        (FStarC_Syntax_Print.term_to_string t)
        (FStarC_Syntax_Print.term_to_string r1)
        (FStarC_Syntax_Print.term_to_string r2);
    r2
  )
  *)

module P = PulseSyntaxExtension_Env

let forall_lid = PulseSyntaxExtension_Env.pulse_lib_core_lid "op_forall_Star"
let stick_lid = FStarC_Ident.lid_of_path ["Pulse"; "Lib"; "Stick"; "op_At_Equals_Equals_Greater"] P.r_
let builtin_lids = [
    FStarC_Parser_Const.and_lid;
    FStarC_Parser_Const.or_lid;
    FStarC_Parser_Const.imp_lid;
    FStarC_Parser_Const.iff_lid;
    FStarC_Parser_Const.forall_lid;
    FStarC_Parser_Const.exists_lid;
    PulseSyntaxExtension_Env.star_lid;
    PulseSyntaxExtension_Env.exists_lid;
    forall_lid;
    stick_lid
]

let deep_transform_to_unary_applications (t:S.term) =
  FStarC_Syntax_Visit.visit_term
    false
    (fun t -> 
      let open S in
      match t.n with
      | Tm_app { hd={n=Tm_fvar {fv_qual=Some (Unresolved_constructor _)}} }
      | Tm_app { hd={n=Tm_fvar {fv_qual=Some (Unresolved_projector _)}} } ->
        t
      | Tm_app { hd; args=_::_::_ as args } -> (
        match (FStarC_Syntax_Util.un_uinst hd).n with
        | Tm_fvar fv
          when FStarC_List.existsb (S.fv_eq_lid fv) builtin_lids ->
          t
        | _ -> 
         List.fold_left (fun t arg -> { t with n = Tm_app {hd=t; args=[arg]} }) hd args
      )
      | _ -> t)
    t

let deep_compress (t:S.term) = FStarC_Syntax_Compress.deep_compress_uvars t
let map_seal (t:'a) (f:'a -> 'b) : 'b = f t
let float_one = FStarC_Util.float_of_string "1.0"
module TcEnv = FStarC_TypeChecker_Env
module Free = FStarC_Syntax_Free
module FlatSet = FStarC_FlatSet

let lax_check_term_with_unknown_universes (g:TcEnv.env) (e:S.term)
  : S.term option
  = let open FStarC_Tactics_V2_Basic in
    let issues, res =
      FStarC_Errors.catch_errors (fun _ ->
        if no_uvars_in_g g &&
          no_uvars_in_term e
        then (
          match e.n with
          | S.Tm_fvar { fv_qual = Some _ } ->
            (* record projectors etc. are pure *)
            None 
          | _ ->
            let g = TcEnv.set_range g e.pos in
            let must_tot = false in
            let g = {g with instantiate_imp=false; phase1=true; admit=true} in
            let e, t, guard = g.typeof_tot_or_gtot_term g e must_tot in
            let _ = FStarC_TypeChecker_Rel.resolve_implicits g guard in
            let uvs = FlatSet.union Free.ord_ctx_uvar (Free.uvars e) (Free.uvars t) in
            if not (FlatSet.is_empty uvs)
            then None
            else (
              let univs = FlatSet.union Free.ord_univ_uvar (Free.univs e) (Free.univs t) in
              let univs = FlatSet.elems univs in
              List.iter (fun univ -> FStarC_Syntax_Unionfind.univ_change univ S.U_unknown) univs;
              let t = FStarC_Syntax_Compress.deep_compress false true t in
              Some t
            )
          )
          else None
      )
    in
    FStarC_Errors.add_issues issues;
    match res with
    | None -> None
    | Some None -> None
    | Some (Some x) -> Some x

let tc_term_phase1 (g:TcEnv.env) (e:S.term) (instantiate_imp:bool) =
  let issues, res = FStarC_Errors.catch_errors (fun _ ->
    let g = TcEnv.set_range g e.pos in
    let g = {g with phase1=true; admit=true; instantiate_imp} in
    let e, c, guard = FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term g e in
    let t = c.res_typ in
    let c = FStarC_TypeChecker_Normalize.maybe_ghost_to_pure_lcomp g c in
    let eff = if FStarC_TypeChecker_Common.is_total_lcomp c then FStarC_TypeChecker_Core.E_Total else FStarC_TypeChecker_Core.E_Ghost in
    let guard = FStarC_TypeChecker_Rel.solve_deferred_constraints g guard in
    let guard = FStarC_TypeChecker_Rel.resolve_implicits g guard in
    e, t, eff) in
  res, issues

let teq_nosmt_force (g:TcEnv.env) (ty1:S.term) (ty2:S.term) =
  let issues, res = FStarC_Errors.catch_errors (fun _ ->
    let g = TcEnv.set_range g ty1.pos in
    let ok = FStarC_TypeChecker_Rel.teq_nosmt_force g ty1 ty2 in
    ok) in
  match res with Some true -> true | _ -> false

let whnf_lax (g:TcEnv.env) (t:S.term) : S.term = 
  FStarC_TypeChecker_Normalize.unfold_whnf' [TcEnv.Unascribe] g t

let hnf_lax (g:TcEnv.env) (t:S.term) : S.term =
  FStarC_TypeChecker_Normalize.normalize [TcEnv.Unascribe; TcEnv.Primops; TcEnv.HNF; TcEnv.UnfoldUntil S.delta_constant; TcEnv.Beta] g t

let norm_well_typed_term_aux
      (g:TcEnv.env)
      (t:S.term)
      (steps:FStarC_NormSteps.norm_step list)
  = let steps = FStarC_TypeChecker_Cfg.translate_norm_steps steps in
    let t' = FStarC_TypeChecker_Normalize.normalize (TcEnv.Unascribe::steps) g t in
    FStar_Pervasives.Mkdtuple3 (t', (), ())

let norm_well_typed_term      
      (g:TcEnv.env)
      (t:S.term)
      (eff:_)
      (k:_)
      (typing:_)
      (steps:FStarC_NormSteps.norm_step list)
      (ps:_)
  = let t' = norm_well_typed_term_aux g t steps in
    FStarC_Tactics_Result.Success (t', ps)

let add_attribute (s:S.sigelt) (x:S.attribute) =
  { s with sigattrs = x::s.sigattrs }
let add_noextract_qual (s:S.sigelt) =
  { s with sigquals = S.NoExtract::s.sigquals }
let get_attributes (s:S.sigelt) (ps:_) =
  FStarC_Tactics_Result.Success (s.sigattrs, ps)

let must_erase_for_extraction (g:FStarC_Reflection_Types.env) (ty:FStarC_Syntax_Syntax.term) =
  FStarC_TypeChecker_Util.must_erase_for_extraction g ty

let magic_s s = failwith ("Cannot execute magic: " ^ s)

let profile (f: unit -> 'b utac) (module_name:string list) (component_name:string) 
: 'b utac
= fun ps ->
    let name = String.concat "." module_name in
    FStarC_Profiling.profile (fun () -> f () ps) (Some name) component_name

module RR = FStarC_Reflection_V2_Builtins
let mk_app_flat (head:S.term) (args:_) r =
  let args = List.map (fun (x, q) -> x, RR.pack_aqual q) args in
  S.mk_Tm_app head args r

let record_stats (key:string) (f: unit -> 'a utac)
: 'a utac
= fun ps ->
    FStarC_Stats.record key (fun () -> f () ps)

let stack_dump () = FStarC_Util.stack_dump()

let push_options () : unit = FStarC_Options.push ()
let pop_options () : unit = FStarC_Options.pop ()
let set_options (opts: string) : unit =
  ignore (FStarC_Options.set_options opts)
