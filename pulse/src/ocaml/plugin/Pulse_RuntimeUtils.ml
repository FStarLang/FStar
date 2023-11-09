type context = ((string * FStar_Range.range option) list) FStar_Sealed.sealed
let extend_context (s:string) (r:FStar_Range.range option) (c:context) = (s,r)::c
let env_set_context (g:FStar_Reflection_Types.env) (c:context) = g
let print_exn (e:exn) = Printexc.to_string e
let debug_at_level_no_module (s:string) = FStar_Options.debug_at_level_no_module (FStar_Options.Other s)
let debug_at_level (g:FStar_Reflection_Types.env) (s:string) = FStar_TypeChecker_Env.debug g (FStar_Options.Other s)
let bv_set_range (bv:FStar_Syntax_Syntax.bv) (r:FStar_Range.range) = FStar_Syntax_Syntax.set_range_of_bv bv r
let bv_range (bv:FStar_Syntax_Syntax.bv) = FStar_Syntax_Syntax.range_of_bv bv
let binder_set_range (b:FStar_Syntax_Syntax.binder) (r:FStar_Range.range) =
    { b with FStar_Syntax_Syntax.binder_bv = (bv_set_range b.FStar_Syntax_Syntax.binder_bv r) }
let binder_range (b:FStar_Syntax_Syntax.binder) = bv_range b.FStar_Syntax_Syntax.binder_bv
let set_range (t:FStar_Syntax_Syntax.term) (r:FStar_Range.range) = { t with FStar_Syntax_Syntax.pos = r}
let set_use_range (t:FStar_Syntax_Syntax.term) (r:FStar_Range.range) = FStar_Syntax_Subst.set_use_range r t
let error_code_uninstantiated_variable () = FStar_Errors.errno FStar_Errors_Codes.Error_UninstantiatedUnificationVarInTactic
let is_range_zero (r:FStar_Range.range) = r = FStar_Range.range_0
let union_ranges (r0:FStar_Range.range) (r1:FStar_Range.range) = FStar_Compiler_Range.union_ranges r0 r1
let range_of_term (t:FStar_Syntax_Syntax.term) = t.FStar_Syntax_Syntax.pos
let unfold_def (g:FStar_Reflection_Types.env) (head:string) (names:string list) (t:FStar_Syntax_Syntax.term) : FStar_Syntax_Syntax.term option =
    let open FStar_TypeChecker_Env in
    Some (FStar_TypeChecker_Normalize.normalize
            [Beta; Iota;
             UnfoldOnly (FStar_Ident.lid_of_str head::List.map FStar_Ident.lid_of_str names)] g t)
let env_set_range (e:FStar_Reflection_Types.env) (r:FStar_Range.range) =
   FStar_TypeChecker_Env.set_range e r

let is_pulse_option_set (x:string) : bool =
  let key = ("pulse:"^x) in
  let value = FStar_Options.ext_getv key in
  value <> ""

module U = FStar_Syntax_Util
module S = FStar_Syntax_Syntax
let embed_st_term_for_extraction (d:'a) r =
   U.mk_lazy d S.tun (S.Lazy_extension "pulse_st_term") r
let unembed_st_term_for_extraction (d:S.term) : 'a =
   U.unlazy_as_t (S.Lazy_extension "pulse_st_term") d

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
  
let deep_transform_to_unary_applications (t:S.term) =
  FStar_Syntax_Visit.visit_term
    (fun t -> 
      let open S in
      match t.n with
      | Tm_app { hd; args=_::_::_ as args } ->
        List.fold_left (fun t arg -> { t with n = Tm_app {hd=t; args=[arg]} }) hd args

      | _ -> t)
    t

let deep_compress (t:S.term) = FStar_Syntax_Compress.deep_compress_uvars t
let map_seal (t:'a) (f:'a -> 'b) : 'b = f t
let float_one = FStar_Compiler_Util.float_of_string "1.0"
module TcEnv = FStar_TypeChecker_Env
module Free = FStar_Syntax_Free
module BU = FStar_Compiler_Util
let lax_check_term_with_unknown_universes (g:TcEnv.env) (e:S.term)
  : S.term option
  = let open FStar_Tactics_V2_Basic in
    let issues, res =
      FStar_Errors.catch_errors (fun _ ->
        if no_uvars_in_g g &&
          no_uvars_in_term e
        then (
          let g = TcEnv.set_range g e.pos in
          let must_tot = false in
          let g = {g with instantiate_imp=false; phase1=true; lax=true} in
          let e, t, guard = g.typeof_tot_or_gtot_term g e must_tot in
          let _ = FStar_TypeChecker_Rel.resolve_implicits g guard in
          let uvs = BU.set_union (Free.uvars e) (Free.uvars t) in
          if not (BU.set_is_empty uvs)
          then None
          else (
            let univs = BU.set_union (Free.univs e) (Free.univs t) in
            let univs = BU.set_elements univs in
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