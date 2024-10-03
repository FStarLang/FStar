type context = ((string * FStar_Range.range option) list) FStar_Sealed.sealed
let extend_context (s:string) (r:FStar_Range.range option) (c:context) = (s,r)::c
module T = FStar_Tactics_Effect
module TR = FStar_Tactics_Result
type 'a utac = ('a, unit) T.tac_repr 
let ctxt_elt_as_string (s, r) =
    match r with
    | None -> s
    | Some r ->
      "@" ^ FStar_Compiler_Range.string_of_range r ^ ": " ^ s
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
      FStar_Errors.with_ctx (ctxt_elt_as_string sr) (fun _ -> f () ps)) ps
let with_error_bound (r:FStar_Range.range) (f: unit -> 'a utac) : 'a utac =
  fun ps ->
    FStar_Errors.with_error_bound r (fun _ -> f () ps)
let disable_admit_smt_queries (f: unit -> 'a utac) : 'a utac =
  fun ps ->
    FStar_Options.with_saved_options (fun _ ->
      FStar_Options.set_option "admit_smt_queries" (FStar_Options.Bool false);
      f () ps
    )
let with_extv (k:string) (v:string) (f: unit -> 'a utac) : 'a utac =
  fun ps ->
    let open FStar_Options_Ext in
    let x = FStar_Options_Ext.save() in
    FStar_Options_Ext.set k v;
    let res = f () ps in
    FStar_Options_Ext.restore x;
    res
let env_set_context (g:FStar_Reflection_Types.env) (c:context) = g
let print_exn (e:exn) = Printexc.to_string e
let debug_at_level_no_module (s:string) =
  let r = FStar_Compiler_Debug.get_toggle s in
  !r
let debug_at_level (g:FStar_Reflection_Types.env) (s:string) =
  let r = FStar_Compiler_Debug.get_toggle s in
  !r

let bv_set_range (bv:FStar_Syntax_Syntax.bv) (r:FStar_Range.range) = FStar_Syntax_Syntax.set_range_of_bv bv r
let bv_range (bv:FStar_Syntax_Syntax.bv) = FStar_Syntax_Syntax.range_of_bv bv
let binder_set_range (b:FStar_Syntax_Syntax.binder) (r:FStar_Range.range) =
    { b with FStar_Syntax_Syntax.binder_bv = (bv_set_range b.FStar_Syntax_Syntax.binder_bv r) }
let binder_range (b:FStar_Syntax_Syntax.binder) = bv_range b.FStar_Syntax_Syntax.binder_bv
let start_of_range (r:FStar_Range.range) =
  let open FStar_Compiler_Range in
  mk_range (file_of_range r) (start_of_range r) (start_of_range r)
  let set_range (t:FStar_Syntax_Syntax.term) (r:FStar_Range.range) = { t with FStar_Syntax_Syntax.pos = r}
let set_use_range (t:FStar_Syntax_Syntax.term) (r:FStar_Range.range) = FStar_Syntax_Subst.set_use_range r t
let error_code_uninstantiated_variable () = FStar_Errors.errno FStar_Errors_Codes.Error_UninstantiatedUnificationVarInTactic
let is_range_zero (r:FStar_Range.range) = r = FStar_Range.range_0
let union_ranges (r0:FStar_Range.range) (r1:FStar_Range.range) = FStar_Compiler_Range.union_ranges r0 r1
let range_of_term (t:FStar_Syntax_Syntax.term) = t.FStar_Syntax_Syntax.pos
let env_set_range (e:FStar_Reflection_Types.env) (r:FStar_Range.range) =
   FStar_TypeChecker_Env.set_range e r

let is_pulse_option_set (x:string) : bool =
  let key = ("pulse:"^x) in
  let value = FStar_Options_Ext.get key in
  value <> ""

module U = FStar_Syntax_Util
module S = FStar_Syntax_Syntax
let embed_st_term_for_extraction (d:'a) r =
   U.mk_lazy d S.tun (S.Lazy_extension "pulse_st_term") r
let unembed_st_term_for_extraction (d:S.term) : 'a =
   U.unlazy_as_t (S.Lazy_extension "pulse_st_term") d
let unembed_pulse_decl (d:'a) : 'b =
   U.unlazy_as_t (S.Lazy_extension "pulse_decl") (Obj.magic d)

let debug_subst (s:S.subst_elt list) (t:S.term) (r1:S.term) (r2:S.term) =
  if is_pulse_option_set "subst"
  then r2
  else r1
  (*
  FStar_Options.debug_at_level_no_module
  let open FStar_Compiler_Util in
  if U.term_eq_dbg true r1 r2
  then r1
  else (
    print4 "Applied subst %s to %s\nExpected %s\nGot %s\n"
        (FStar_Syntax_Print.subst_to_string s)
        (FStar_Syntax_Print.term_to_string t)
        (FStar_Syntax_Print.term_to_string r1)
        (FStar_Syntax_Print.term_to_string r2);
    r2
  )
  *)

module P = PulseSyntaxExtension_Env

let forall_lid = PulseSyntaxExtension_Env.pulse_lib_core_lid "op_forall_Star"
let stick_lid = FStar_Ident.lid_of_path ["Pulse"; "Lib"; "Stick"; "op_At_Equals_Equals_Greater"] P.r_
let builtin_lids = [
    FStar_Parser_Const.and_lid;
    FStar_Parser_Const.or_lid;
    FStar_Parser_Const.imp_lid;
    FStar_Parser_Const.iff_lid;
    FStar_Parser_Const.forall_lid;
    FStar_Parser_Const.exists_lid;
    PulseSyntaxExtension_Env.star_lid;
    PulseSyntaxExtension_Env.exists_lid;
    forall_lid;
    stick_lid
]

let deep_transform_to_unary_applications (t:S.term) =
  FStar_Syntax_Visit.visit_term
    false
    (fun t -> 
      let open S in
      match t.n with
      | Tm_app { hd={n=Tm_fvar {fv_qual=Some (Unresolved_constructor _)}} }
      | Tm_app { hd={n=Tm_fvar {fv_qual=Some (Unresolved_projector _)}} } ->
        t
      | Tm_app { hd; args=_::_::_ as args } -> (
        match (FStar_Syntax_Util.un_uinst hd).n with
        | Tm_fvar fv
          when FStar_Compiler_List.existsb (S.fv_eq_lid fv) builtin_lids ->
          t
        | _ -> 
         List.fold_left (fun t arg -> { t with n = Tm_app {hd=t; args=[arg]} }) hd args
      )
      | _ -> t)
    t

let deep_compress (t:S.term) = FStar_Syntax_Compress.deep_compress_uvars t
let map_seal (t:'a) (f:'a -> 'b) : 'b = f t
let float_one = FStar_Compiler_Util.float_of_string "1.0"
module TcEnv = FStar_TypeChecker_Env
module Free = FStar_Syntax_Free
module BU = FStar_Compiler_Util
module FlatSet = FStar_Compiler_FlatSet

let lax_check_term_with_unknown_universes (g:TcEnv.env) (e:S.term)
  : S.term option
  = let open FStar_Tactics_V2_Basic in
    let issues, res =
      FStar_Errors.catch_errors (fun _ ->
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
            let _ = FStar_TypeChecker_Rel.resolve_implicits g guard in
            let uvs = FlatSet.union Free.ord_ctx_uvar (Free.uvars e) (Free.uvars t) in
            if not (FlatSet.is_empty uvs)
            then None
            else (
              let univs = FlatSet.union Free.ord_univ_uvar (Free.univs e) (Free.univs t) in
              let univs = FlatSet.elems univs in
              List.iter (fun univ -> FStar_Syntax_Unionfind.univ_change univ S.U_unknown) univs;
              let t = FStar_Syntax_Compress.deep_compress false true t in
              Some t
            )
          )
          else None
      )
    in
    FStar_Errors.add_issues issues;
    match res with
    | None -> None
    | Some None -> None
    | Some (Some x) -> Some x

let whnf_lax (g:TcEnv.env) (t:S.term) : S.term = 
  FStar_TypeChecker_Normalize.unfold_whnf' [TcEnv.Unascribe] g t

let hnf_lax (g:TcEnv.env) (t:S.term) : S.term =
  FStar_TypeChecker_Normalize.normalize [TcEnv.Unascribe; TcEnv.Primops; TcEnv.HNF; TcEnv.UnfoldUntil S.delta_constant; TcEnv.Beta] g t

let norm_well_typed_term_aux
      (g:TcEnv.env)
      (t:S.term)
      (steps:FStar_Pervasives.norm_step list)
  = let steps = FStar_TypeChecker_Cfg.translate_norm_steps steps in
    let t' = FStar_TypeChecker_Normalize.normalize (TcEnv.Unascribe::steps) g t in
    FStar_Pervasives.Mkdtuple3 (t', (), ())

let norm_well_typed_term      
      (g:TcEnv.env)
      (t:S.term)
      (eff:_)
      (k:_)
      (typing:_)
      (steps:FStar_Pervasives.norm_step list)
      (ps:_)
  = let t' = norm_well_typed_term_aux g t steps in
    FStar_Tactics_Result.Success (t', ps)

let add_attribute (s:S.sigelt) (x:S.attribute) =
  { s with sigattrs = x::s.sigattrs }
let add_noextract_qual (s:S.sigelt) =
  { s with sigquals = S.NoExtract::s.sigquals }
let get_attributes (s:S.sigelt) (ps:_) =
  FStar_Tactics_Result.Success (s.sigattrs, ps)

let must_erase_for_extraction (g:FStar_Reflection_Types.env) (ty:FStar_Syntax_Syntax.term) =
  FStar_TypeChecker_Util.must_erase_for_extraction g ty

let magic_s s = failwith ("Cannot execute magic: " ^ s)