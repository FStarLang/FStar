type context = ((string * FStar_Range.range option) list) FStar_Sealed.sealed
let extend_context (s:string) (r:FStar_Range.range option) (c:context) = (s,r)::c
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
let embed_term_for_extraction (d:'a) typ r =
   U.mk_lazy d typ (S.Lazy_extension "pulse") r

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