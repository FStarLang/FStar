open Prims
type error = (Prims.string * FStar_Compiler_Range_Type.range)
type 'a err = ('a, error) FStar_Pervasives.either
let op_let_Question :
  'a 'b . 'a err -> ('a -> 'b err) -> ('b, error) FStar_Pervasives.either =
  fun f ->
    fun g ->
      match f with
      | FStar_Pervasives.Inl a1 -> g a1
      | FStar_Pervasives.Inr e -> FStar_Pervasives.Inr e
let return : 'a . 'a -> 'a err = fun x -> FStar_Pervasives.Inl x
let fail : 'a . Prims.string -> FStar_Compiler_Range_Type.range -> 'a err =
  fun message -> fun range -> FStar_Pervasives.Inr (message, range)
let rec map_err :
  'a 'b . ('a -> 'b err) -> 'a Prims.list -> 'b Prims.list err =
  fun f ->
    fun l ->
      match l with
      | [] -> return []
      | hd::tl ->
          let uu___ = f hd in
          op_let_Question uu___
            (fun hd1 ->
               let uu___1 = map_err f tl in
               op_let_Question uu___1 (fun tl1 -> return (hd1 :: tl1)))
let map_err_opt :
  'a 'b .
    ('a -> 'b err) ->
      'a FStar_Pervasives_Native.option ->
        'b FStar_Pervasives_Native.option err
  =
  fun f ->
    fun o ->
      match o with
      | FStar_Pervasives_Native.None -> return FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some v ->
          let uu___ = f v in
          op_let_Question uu___
            (fun v' -> return (FStar_Pervasives_Native.Some v'))
let (as_term : FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.term) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_unknown ->
        PulseSyntaxWrapper.tm_unknown t.FStar_Syntax_Syntax.pos
    | uu___ -> PulseSyntaxWrapper.tm_expr t t.FStar_Syntax_Syntax.pos
type env_t =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  local_refs: FStar_Ident.ident Prims.list }
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee -> match projectee with | { tcenv; local_refs;_} -> tcenv
let (__proj__Mkenv_t__item__local_refs :
  env_t -> FStar_Ident.ident Prims.list) =
  fun projectee ->
    match projectee with | { tcenv; local_refs;_} -> local_refs
let (push_bv :
  env_t -> FStar_Ident.ident -> (env_t * FStar_Syntax_Syntax.bv)) =
  fun env ->
    fun x ->
      let uu___ =
        FStar_Syntax_DsEnv.push_bv (env.tcenv).FStar_TypeChecker_Env.dsenv x in
      match uu___ with
      | (dsenv, bv) ->
          let tcenv =
            let uu___1 = env.tcenv in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = (uu___1.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.intactics =
                (uu___1.FStar_TypeChecker_Env.intactics);
              FStar_TypeChecker_Env.tc_term =
                (uu___1.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                (uu___1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStar_TypeChecker_Env.universe_of =
                (uu___1.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (uu___1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStar_TypeChecker_Env.teq_nosmt_force =
                (uu___1.FStar_TypeChecker_Env.teq_nosmt_force);
              FStar_TypeChecker_Env.subtype_nosmt_force =
                (uu___1.FStar_TypeChecker_Env.subtype_nosmt_force);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv = dsenv;
              FStar_TypeChecker_Env.nbe = (uu___1.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
              FStar_TypeChecker_Env.unif_allow_ref_guards =
                (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards);
              FStar_TypeChecker_Env.erase_erasable_args =
                (uu___1.FStar_TypeChecker_Env.erase_erasable_args);
              FStar_TypeChecker_Env.core_check =
                (uu___1.FStar_TypeChecker_Env.core_check)
            } in
          let env1 = { tcenv; local_refs = (env.local_refs) } in (env1, bv)
let rec (push_bvs :
  env_t ->
    FStar_Ident.ident Prims.list ->
      (env_t * FStar_Syntax_Syntax.bv Prims.list))
  =
  fun env ->
    fun xs ->
      match xs with
      | [] -> (env, [])
      | x::xs1 ->
          let uu___ = push_bv env x in
          (match uu___ with
           | (env1, bv) ->
               let uu___1 = push_bvs env1 xs1 in
               (match uu___1 with | (env2, bvs) -> (env2, (bv :: bvs))))
let (push_namespace : env_t -> FStar_Ident.lident -> env_t) =
  fun env ->
    fun lid ->
      let dsenv =
        FStar_Syntax_DsEnv.push_namespace
          (env.tcenv).FStar_TypeChecker_Env.dsenv lid in
      let tcenv =
        let uu___ = env.tcenv in
        {
          FStar_TypeChecker_Env.solver = (uu___.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range = (uu___.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma = (uu___.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab = (uu___.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq_strict =
            (uu___.FStar_TypeChecker_Env.use_eq_strict);
          FStar_TypeChecker_Env.is_iface =
            (uu___.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit = (uu___.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax = (uu___.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 = (uu___.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard =
            (uu___.FStar_TypeChecker_Env.failhard);
          FStar_TypeChecker_Env.nosynth =
            (uu___.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.intactics =
            (uu___.FStar_TypeChecker_Env.intactics);
          FStar_TypeChecker_Env.tc_term =
            (uu___.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
            (uu___.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
          FStar_TypeChecker_Env.universe_of =
            (uu___.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
            (uu___.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
          FStar_TypeChecker_Env.teq_nosmt_force =
            (uu___.FStar_TypeChecker_Env.teq_nosmt_force);
          FStar_TypeChecker_Env.subtype_nosmt_force =
            (uu___.FStar_TypeChecker_Env.subtype_nosmt_force);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.try_solve_implicits_hook =
            (uu___.FStar_TypeChecker_Env.try_solve_implicits_hook);
          FStar_TypeChecker_Env.splice = (uu___.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.mpreprocess =
            (uu___.FStar_TypeChecker_Env.mpreprocess);
          FStar_TypeChecker_Env.postprocess =
            (uu___.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.identifier_info =
            (uu___.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv = dsenv;
          FStar_TypeChecker_Env.nbe = (uu___.FStar_TypeChecker_Env.nbe);
          FStar_TypeChecker_Env.strict_args_tab =
            (uu___.FStar_TypeChecker_Env.strict_args_tab);
          FStar_TypeChecker_Env.erasable_types_tab =
            (uu___.FStar_TypeChecker_Env.erasable_types_tab);
          FStar_TypeChecker_Env.enable_defer_to_tac =
            (uu___.FStar_TypeChecker_Env.enable_defer_to_tac);
          FStar_TypeChecker_Env.unif_allow_ref_guards =
            (uu___.FStar_TypeChecker_Env.unif_allow_ref_guards);
          FStar_TypeChecker_Env.erase_erasable_args =
            (uu___.FStar_TypeChecker_Env.erase_erasable_args);
          FStar_TypeChecker_Env.core_check =
            (uu___.FStar_TypeChecker_Env.core_check)
        } in
      let env1 = { tcenv; local_refs = (env.local_refs) } in env1
let (desugar_const : FStar_Const.sconst -> PulseSyntaxWrapper.constant) =
  fun c -> PulseSyntaxWrapper.inspect_const c
let (r_ : FStar_Compiler_Range_Type.range) =
  FStar_Compiler_Range_Type.dummyRange
let (admit_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Prims"; "admit"] r_
let (pulse_lib_core_lid : Prims.string -> FStar_Ident.lident) =
  fun l ->
    FStar_Ident.lid_of_path
      (FStar_List_Tot_Base.op_At ["Pulse"; "Lib"; "Core"] [l]) r_
let (pulse_lib_ref_lid : Prims.string -> FStar_Ident.lident) =
  fun l ->
    FStar_Ident.lid_of_path
      (FStar_List_Tot_Base.op_At ["Pulse"; "Lib"; "Reference"] [l]) r_
let (star_lid : FStar_Ident.lident) = pulse_lib_core_lid "op_Star_Star"
let (emp_lid : FStar_Ident.lident) = pulse_lib_core_lid "emp"
let (pure_lid : FStar_Ident.lident) = pulse_lib_core_lid "pure"
let (stt_lid : FStar_Ident.lident) = pulse_lib_core_lid "stt"
let (assign_lid : FStar_Ident.lident) = pulse_lib_ref_lid "op_Colon_Equals"
let (stt_ghost_lid : FStar_Ident.lident) = pulse_lib_core_lid "stt_ghost"
let (stt_atomic_lid : FStar_Ident.lident) = pulse_lib_core_lid "stt_atomic"
let (op_colon_equals_lid :
  FStar_Compiler_Range_Type.range -> FStar_Ident.lident) =
  fun r -> FStar_Ident.lid_of_path ["op_Colon_Equals"] r
let (stapp_assignment :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        PulseSyntaxWrapper.range -> PulseSyntaxWrapper.st_term)
  =
  fun assign_lid1 ->
    fun lhs ->
      fun rhs ->
        fun r ->
          let head_fv =
            FStar_Syntax_Syntax.lid_as_fv assign_lid1
              FStar_Pervasives_Native.None in
          let head = FStar_Syntax_Syntax.fv_to_tm head_fv in
          let app =
            FStar_Syntax_Syntax.mk_Tm_app head
              [(lhs, FStar_Pervasives_Native.None)]
              lhs.FStar_Syntax_Syntax.pos in
          let uu___ = PulseSyntaxWrapper.tm_expr app r in
          let uu___1 = as_term rhs in
          PulseSyntaxWrapper.tm_st_app uu___ FStar_Pervasives_Native.None
            uu___1 r
let (resolve_lid : env_t -> FStar_Ident.lident -> FStar_Ident.lident err) =
  fun env ->
    fun lid ->
      let uu___ =
        FStar_Syntax_DsEnv.try_lookup_lid
          (env.tcenv).FStar_TypeChecker_Env.dsenv lid in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_lid lid in
            FStar_Compiler_Util.format1 "Name %s not found" uu___2 in
          let uu___2 = FStar_Ident.range_of_lid lid in fail uu___1 uu___2
      | FStar_Pervasives_Native.Some t ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Subst.compress t in
            uu___2.FStar_Syntax_Syntax.n in
          (match uu___1 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu___2 = FStar_Syntax_Syntax.lid_of_fv fv in return uu___2
           | uu___2 ->
               let uu___3 =
                 let uu___4 = FStar_Ident.string_of_lid lid in
                 let uu___5 = FStar_Syntax_Print.term_to_string t in
                 FStar_Compiler_Util.format2
                   "Name %s resolved unexpectedly to %s" uu___4 uu___5 in
               let uu___4 = FStar_Ident.range_of_lid lid in
               fail uu___3 uu___4)
let (pulse_arrow_formals :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder Prims.list FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStar_Syntax_Util.arrow_formals_comp_ln t in
    match uu___ with
    | (formals, comp) ->
        let uu___1 = FStar_Syntax_Util.is_total_comp comp in
        if uu___1
        then
          let res = FStar_Syntax_Util.comp_result comp in
          let uu___2 = FStar_Syntax_Util.head_and_args_full res in
          (match uu___2 with
           | (head, uu___3) ->
               let uu___4 =
                 let uu___5 = FStar_Syntax_Subst.compress head in
                 uu___5.FStar_Syntax_Syntax.n in
               (match uu___4 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu___5 =
                      FStar_Compiler_List.existsML
                        (FStar_Syntax_Syntax.fv_eq_lid fv)
                        [stt_lid; stt_ghost_lid; stt_atomic_lid] in
                    if uu___5
                    then FStar_Pervasives_Native.Some formals
                    else FStar_Pervasives_Native.None
                | FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu___5;
                       FStar_Syntax_Syntax.vars = uu___6;
                       FStar_Syntax_Syntax.hash_code = uu___7;_},
                     uu___8)
                    ->
                    let uu___9 =
                      FStar_Compiler_List.existsML
                        (FStar_Syntax_Syntax.fv_eq_lid fv)
                        [stt_lid; stt_ghost_lid; stt_atomic_lid] in
                    if uu___9
                    then FStar_Pervasives_Native.Some formals
                    else FStar_Pervasives_Native.None
                | uu___5 -> FStar_Pervasives_Native.None))
        else FStar_Pervasives_Native.None
let (ret : FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.st_term) =
  fun s ->
    let uu___ = as_term s in
    PulseSyntaxWrapper.tm_return uu___ s.FStar_Syntax_Syntax.pos
type stapp_or_return_t =
  | STTerm of PulseSyntaxWrapper.st_term 
  | Return of FStar_Syntax_Syntax.term 
let (uu___is_STTerm : stapp_or_return_t -> Prims.bool) =
  fun projectee -> match projectee with | STTerm _0 -> true | uu___ -> false
let (__proj__STTerm__item___0 :
  stapp_or_return_t -> PulseSyntaxWrapper.st_term) =
  fun projectee -> match projectee with | STTerm _0 -> _0
let (uu___is_Return : stapp_or_return_t -> Prims.bool) =
  fun projectee -> match projectee with | Return _0 -> true | uu___ -> false
let (__proj__Return__item___0 :
  stapp_or_return_t -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Return _0 -> _0
let (st_term_of_stapp_or_return :
  stapp_or_return_t -> PulseSyntaxWrapper.st_term) =
  fun t -> match t with | STTerm t1 -> t1 | Return t1 -> ret t1
let (stapp_or_return :
  env_t -> FStar_Syntax_Syntax.term -> stapp_or_return_t) =
  fun env ->
    fun s ->
      let r = s.FStar_Syntax_Syntax.pos in
      let uu___ = FStar_Syntax_Util.head_and_args_full s in
      match uu___ with
      | (head, args) ->
          (match head.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu___1 = FStar_Syntax_Syntax.fv_eq_lid fv admit_lid in
               if uu___1
               then
                 let uu___2 = PulseSyntaxWrapper.tm_admit r in STTerm uu___2
               else
                 (let uu___3 =
                    FStar_TypeChecker_Env.try_lookup_lid env.tcenv
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  match uu___3 with
                  | FStar_Pervasives_Native.None -> Return s
                  | FStar_Pervasives_Native.Some ((uu___4, t), uu___5) ->
                      let uu___6 = pulse_arrow_formals t in
                      (match uu___6 with
                       | FStar_Pervasives_Native.None -> Return s
                       | FStar_Pervasives_Native.Some formals ->
                           let is_binder_implicit b =
                             match b.FStar_Syntax_Syntax.binder_qual with
                             | FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Implicit uu___7) ->
                                 true
                             | uu___7 -> false in
                           let is_arg_implicit aq =
                             match FStar_Pervasives_Native.snd aq with
                             | FStar_Pervasives_Native.Some
                                 { FStar_Syntax_Syntax.aqual_implicit = b;
                                   FStar_Syntax_Syntax.aqual_attributes =
                                     uu___7;_}
                                 -> b
                             | uu___7 -> false in
                           let rec uninst_formals formals1 args1 =
                             match (formals1, args1) with
                             | (uu___7, []) ->
                                 FStar_Pervasives_Native.Some formals1
                             | ([], uu___7) -> FStar_Pervasives_Native.None
                             | (f::formals2, a::args2) ->
                                 if is_binder_implicit f
                                 then
                                   (if is_arg_implicit a
                                    then uninst_formals formals2 args2
                                    else uninst_formals formals2 (a :: args2))
                                 else
                                   if is_arg_implicit a
                                   then FStar_Pervasives_Native.None
                                   else uninst_formals formals2 args2 in
                           let uu___7 = uninst_formals formals args in
                           (match uu___7 with
                            | FStar_Pervasives_Native.None -> Return s
                            | FStar_Pervasives_Native.Some formals1 ->
                                let uu___8 =
                                  FStar_Compiler_List.for_all
                                    is_binder_implicit formals1 in
                                if uu___8
                                then
                                  let head1 =
                                    let uu___9 =
                                      FStar_Compiler_List.init args in
                                    FStar_Syntax_Syntax.mk_Tm_app head uu___9
                                      s.FStar_Syntax_Syntax.pos in
                                  let uu___9 = FStar_Compiler_List.last args in
                                  (match uu___9 with
                                   | (last, q) ->
                                       let uu___10 =
                                         let uu___11 =
                                           PulseSyntaxWrapper.tm_expr head1
                                             head1.FStar_Syntax_Syntax.pos in
                                         let uu___12 = as_term last in
                                         PulseSyntaxWrapper.tm_st_app uu___11
                                           q uu___12 r in
                                       STTerm uu___10)
                                else Return s)))
           | uu___1 -> Return s)
let (tosyntax' :
  env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term err) =
  fun env ->
    fun t ->
      try
        (fun uu___ ->
           match () with
           | () ->
               let uu___1 =
                 FStar_ToSyntax_ToSyntax.desugar_term
                   (env.tcenv).FStar_TypeChecker_Env.dsenv t in
               return uu___1) ()
      with
      | uu___ ->
          let uu___1 = FStar_Errors.issue_of_exn uu___ in
          (match uu___1 with
           | FStar_Pervasives_Native.Some i ->
               (FStar_Errors.add_issues [i];
                fail "Failed to desugar Pulse term" t.FStar_Parser_AST.range)
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 let uu___3 = FStar_Parser_AST.term_to_string t in
                 let uu___4 = PulseSyntaxWrapper.print_exn uu___ in
                 FStar_Compiler_Util.format2
                   "Failed to desugar Pulse term %s\nUnexpected exception: %s\n"
                   uu___3 uu___4 in
               fail uu___2 t.FStar_Parser_AST.range)
let (tosyntax :
  env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term err) =
  fun env ->
    fun t ->
      let uu___ = tosyntax' env t in
      op_let_Question uu___ (fun s -> return s)
let (desugar_term :
  env_t -> FStar_Parser_AST.term -> PulseSyntaxWrapper.term err) =
  fun env ->
    fun t ->
      let uu___ = tosyntax env t in
      op_let_Question uu___
        (fun s -> let uu___1 = as_term s in return uu___1)
let (desugar_term_opt :
  env_t ->
    FStar_Parser_AST.term FStar_Pervasives_Native.option ->
      PulseSyntaxWrapper.term err)
  =
  fun env ->
    fun t ->
      match t with
      | FStar_Pervasives_Native.None ->
          let uu___ =
            PulseSyntaxWrapper.tm_unknown
              FStar_Compiler_Range_Type.dummyRange in
          return uu___
      | FStar_Pervasives_Native.Some e -> desugar_term env e
let (interpret_vprop_constructors :
  env_t -> FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.term) =
  fun env ->
    fun v ->
      let uu___ = FStar_Syntax_Util.head_and_args_full v in
      match uu___ with
      | (head, args) ->
          (match ((head.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___1)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv pure_lid ->
               let res =
                 let uu___2 = as_term l in
                 PulseSyntaxWrapper.tm_pure uu___2 v.FStar_Syntax_Syntax.pos in
               res
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv emp_lid ->
               PulseSyntaxWrapper.tm_emp v.FStar_Syntax_Syntax.pos
           | uu___1 -> as_term v)
let rec (desugar_vprop :
  env_t -> PulseSugar.vprop -> PulseSyntaxWrapper.vprop err) =
  fun env ->
    fun v ->
      match v.PulseSugar.v with
      | PulseSugar.VPropTerm t ->
          let uu___ = tosyntax env t in
          op_let_Question uu___
            (fun t1 ->
               let uu___1 = interpret_vprop_constructors env t1 in
               return uu___1)
      | PulseSugar.VPropStar (v1, v2) ->
          let uu___ = desugar_vprop env v1 in
          op_let_Question uu___
            (fun v11 ->
               let uu___1 = desugar_vprop env v2 in
               op_let_Question uu___1
                 (fun v21 ->
                    let uu___2 =
                      PulseSyntaxWrapper.tm_star v11 v21 v.PulseSugar.vrange in
                    return uu___2))
      | PulseSugar.VPropExists
          { PulseSugar.binders = binders; PulseSugar.body = body;_} ->
          let rec aux env1 binders1 =
            match binders1 with
            | [] -> desugar_vprop env1 body
            | (uu___, i, t)::bs ->
                let uu___1 = desugar_term env1 t in
                op_let_Question uu___1
                  (fun t1 ->
                     let uu___2 = push_bv env1 i in
                     match uu___2 with
                     | (env2, bv) ->
                         let uu___3 = aux env2 bs in
                         op_let_Question uu___3
                           (fun body1 ->
                              let body2 =
                                PulseSyntaxWrapper.close_term body1
                                  bv.FStar_Syntax_Syntax.index in
                              let b = PulseSyntaxWrapper.mk_binder i t1 in
                              let uu___4 =
                                PulseSyntaxWrapper.tm_exists b body2
                                  v.PulseSugar.vrange in
                              return uu___4)) in
          aux env binders
let (mk_totbind :
  PulseSyntaxWrapper.binder ->
    PulseSyntaxWrapper.term ->
      PulseSyntaxWrapper.st_term ->
        PulseSyntaxWrapper.range -> PulseSyntaxWrapper.st_term)
  =
  fun b ->
    fun s1 -> fun s2 -> fun r -> PulseSyntaxWrapper.tm_totbind b s1 s2 r
let (mk_bind :
  PulseSyntaxWrapper.binder ->
    PulseSyntaxWrapper.st_term ->
      PulseSyntaxWrapper.st_term ->
        PulseSyntaxWrapper.range -> PulseSyntaxWrapper.st_term)
  =
  fun b -> fun s1 -> fun s2 -> fun r -> PulseSyntaxWrapper.tm_bind b s1 s2 r
let (explicit_rvalues : env_t -> PulseSugar.stmt -> PulseSugar.stmt) =
  fun env -> fun s -> s
type qual = PulseSyntaxWrapper.qualifier FStar_Pervasives_Native.option
let (as_qual : FStar_Parser_AST.aqual -> qual) =
  fun q ->
    match q with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
        PulseSyntaxWrapper.as_qual true
    | uu___ -> PulseSyntaxWrapper.as_qual false
let (resolve_names :
  env_t ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option err)
  =
  fun env ->
    fun ns ->
      match ns with
      | FStar_Pervasives_Native.None -> return FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some ns1 ->
          let uu___ = map_err (resolve_lid env) ns1 in
          op_let_Question uu___
            (fun ns2 -> return (FStar_Pervasives_Native.Some ns2))
let (resolve_hint_type :
  env_t -> PulseSugar.hint_type -> PulseSugar.hint_type err) =
  fun env ->
    fun ht ->
      match ht with
      | PulseSugar.ASSERT -> return PulseSugar.ASSERT
      | PulseSugar.UNFOLD ns ->
          let uu___ = resolve_names env ns in
          op_let_Question uu___ (fun ns1 -> return (PulseSugar.UNFOLD ns1))
      | PulseSugar.FOLD ns ->
          let uu___ = resolve_names env ns in
          op_let_Question uu___ (fun ns1 -> return (PulseSugar.FOLD ns1))
let (desugar_datacon : env_t -> FStar_Ident.lid -> PulseSyntaxWrapper.fv err)
  =
  fun env ->
    fun l ->
      let rng = FStar_Ident.range_of_lid l in
      let t =
        FStar_Parser_AST.mk_term (FStar_Parser_AST.Name l) rng
          FStar_Parser_AST.Expr in
      let uu___ = tosyntax env t in
      op_let_Question uu___
        (fun tt ->
           let uu___1 =
             let uu___2 =
               let uu___3 = FStar_Syntax_Subst.compress tt in
               uu___3.FStar_Syntax_Syntax.n in
             match uu___2 with
             | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Pervasives.Inl fv
             | FStar_Syntax_Syntax.Tm_uinst
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu___3;
                    FStar_Syntax_Syntax.vars = uu___4;
                    FStar_Syntax_Syntax.hash_code = uu___5;_},
                  uu___6)
                 -> FStar_Pervasives.Inl fv
             | uu___3 ->
                 let uu___4 =
                   let uu___5 = FStar_Ident.string_of_lid l in
                   FStar_Compiler_Util.format1 "Not a datacon? %s" uu___5 in
                 fail uu___4 rng in
           op_let_Question uu___1
             (fun sfv ->
                let uu___2 =
                  let uu___3 = FStar_Syntax_Syntax.lid_of_fv sfv in
                  PulseSyntaxWrapper.mk_fv uu___3 rng in
                FStar_Pervasives.Inl uu___2))
let rec (desugar_stmt :
  env_t -> PulseSugar.stmt -> PulseSyntaxWrapper.st_term err) =
  fun env ->
    fun s ->
      match s.PulseSugar.s with
      | PulseSugar.Expr { PulseSugar.e = e;_} ->
          let uu___ = tosyntax env e in
          op_let_Question uu___
            (fun tm ->
               let uu___1 =
                 let uu___2 = stapp_or_return env tm in
                 st_term_of_stapp_or_return uu___2 in
               return uu___1)
      | PulseSugar.Assignment
          { PulseSugar.lhs = lhs; PulseSugar.value = value;_} ->
          let uu___ = tosyntax env lhs in
          op_let_Question uu___
            (fun lhs1 ->
               let uu___1 = tosyntax env value in
               op_let_Question uu___1
                 (fun rhs ->
                    let uu___2 =
                      let uu___3 = op_colon_equals_lid s.PulseSugar.range1 in
                      resolve_lid env uu___3 in
                    op_let_Question uu___2
                      (fun assignment_lid ->
                         let uu___3 =
                           stapp_assignment assignment_lid lhs1 rhs
                             s.PulseSugar.range1 in
                         return uu___3)))
      | PulseSugar.Sequence
          {
            PulseSugar.s1 =
              { PulseSugar.s = PulseSugar.Open l;
                PulseSugar.range1 = uu___;_};
            PulseSugar.s2 = s2;_}
          -> let env1 = push_namespace env l in desugar_stmt env1 s2
      | PulseSugar.Sequence
          {
            PulseSugar.s1 =
              { PulseSugar.s = PulseSugar.LetBinding lb;
                PulseSugar.range1 = uu___;_};
            PulseSugar.s2 = s2;_}
          -> desugar_bind env lb s2 s.PulseSugar.range1
      | PulseSugar.ProofHintWithBinders uu___ ->
          desugar_assert_with_binders env s FStar_Pervasives_Native.None
            s.PulseSugar.range1
      | PulseSugar.Sequence { PulseSugar.s1 = s1; PulseSugar.s2 = s2;_} when
          PulseSugar.uu___is_ProofHintWithBinders s1.PulseSugar.s ->
          desugar_assert_with_binders env s1
            (FStar_Pervasives_Native.Some s2) s.PulseSugar.range1
      | PulseSugar.Sequence { PulseSugar.s1 = s1; PulseSugar.s2 = s2;_} ->
          desugar_sequence env s1 s2 s.PulseSugar.range1
      | PulseSugar.Block { PulseSugar.stmt = stmt;_} -> desugar_stmt env stmt
      | PulseSugar.If
          { PulseSugar.head1 = head; PulseSugar.join_vprop = join_vprop;
            PulseSugar.then_ = then_; PulseSugar.else_opt = else_opt;_}
          ->
          let uu___ = desugar_term env head in
          op_let_Question uu___
            (fun head1 ->
               let uu___1 =
                 match join_vprop with
                 | FStar_Pervasives_Native.None ->
                     return FStar_Pervasives_Native.None
                 | FStar_Pervasives_Native.Some t ->
                     let uu___2 = desugar_vprop env t in
                     op_let_Question uu___2
                       (fun vp -> return (FStar_Pervasives_Native.Some vp)) in
               op_let_Question uu___1
                 (fun join_vprop1 ->
                    let uu___2 = desugar_stmt env then_ in
                    op_let_Question uu___2
                      (fun then_1 ->
                         let uu___3 =
                           match else_opt with
                           | FStar_Pervasives_Native.None ->
                               let uu___4 =
                                 let uu___5 =
                                   PulseSyntaxWrapper.tm_expr
                                     FStar_Syntax_Syntax.unit_const
                                     FStar_Compiler_Range_Type.dummyRange in
                                 PulseSyntaxWrapper.tm_return uu___5
                                   FStar_Compiler_Range_Type.dummyRange in
                               return uu___4
                           | FStar_Pervasives_Native.Some e ->
                               desugar_stmt env e in
                         op_let_Question uu___3
                           (fun else_ ->
                              let uu___4 =
                                PulseSyntaxWrapper.tm_if head1 join_vprop1
                                  then_1 else_ s.PulseSugar.range1 in
                              return uu___4))))
      | PulseSugar.Match
          { PulseSugar.head2 = head;
            PulseSugar.returns_annot = returns_annot;
            PulseSugar.branches = branches;_}
          ->
          let uu___ = desugar_term env head in
          op_let_Question uu___
            (fun head1 ->
               let uu___1 = map_err_opt (desugar_vprop env) returns_annot in
               op_let_Question uu___1
                 (fun returns_annot1 ->
                    let uu___2 = map_err (desugar_branch env) branches in
                    op_let_Question uu___2
                      (fun branches1 ->
                         let uu___3 =
                           PulseSyntaxWrapper.tm_match head1 returns_annot1
                             branches1 s.PulseSugar.range1 in
                         return uu___3)))
      | PulseSugar.While
          { PulseSugar.guard = guard; PulseSugar.id1 = id;
            PulseSugar.invariant = invariant; PulseSugar.body1 = body;_}
          ->
          let uu___ = desugar_stmt env guard in
          op_let_Question uu___
            (fun guard1 ->
               let uu___1 =
                 let uu___2 = push_bv env id in
                 match uu___2 with
                 | (env1, bv) ->
                     let uu___3 = desugar_vprop env1 invariant in
                     op_let_Question uu___3
                       (fun inv ->
                          let uu___4 =
                            PulseSyntaxWrapper.close_term inv
                              bv.FStar_Syntax_Syntax.index in
                          return uu___4) in
               op_let_Question uu___1
                 (fun invariant1 ->
                    let uu___2 = desugar_stmt env body in
                    op_let_Question uu___2
                      (fun body1 ->
                         let uu___3 =
                           PulseSyntaxWrapper.tm_while guard1
                             (id, invariant1) body1 s.PulseSugar.range1 in
                         return uu___3)))
      | PulseSugar.Introduce
          { PulseSugar.vprop = vprop; PulseSugar.witnesses = witnesses;_} ->
          (match vprop.PulseSugar.v with
           | PulseSugar.VPropTerm uu___ ->
               fail "introduce expects an existential formula"
                 s.PulseSugar.range1
           | PulseSugar.VPropExists uu___ ->
               let uu___1 = desugar_vprop env vprop in
               op_let_Question uu___1
                 (fun vp ->
                    let uu___2 = map_err (desugar_term env) witnesses in
                    op_let_Question uu___2
                      (fun witnesses1 ->
                         let uu___3 =
                           PulseSyntaxWrapper.tm_intro_exists vp witnesses1
                             s.PulseSugar.range1 in
                         return uu___3)))
      | PulseSugar.Parallel
          { PulseSugar.p1 = p1; PulseSugar.p2 = p2; PulseSugar.q1 = q1;
            PulseSugar.q2 = q2; PulseSugar.b1 = b1; PulseSugar.b2 = b2;_}
          ->
          let uu___ = desugar_vprop env p1 in
          op_let_Question uu___
            (fun p11 ->
               let uu___1 = desugar_vprop env p2 in
               op_let_Question uu___1
                 (fun p21 ->
                    let uu___2 = desugar_vprop env q1 in
                    op_let_Question uu___2
                      (fun q11 ->
                         let uu___3 = desugar_vprop env q2 in
                         op_let_Question uu___3
                           (fun q21 ->
                              let uu___4 = desugar_stmt env b1 in
                              op_let_Question uu___4
                                (fun b11 ->
                                   let uu___5 = desugar_stmt env b2 in
                                   op_let_Question uu___5
                                     (fun b21 ->
                                        let uu___6 =
                                          PulseSyntaxWrapper.tm_par p11 p21
                                            q11 q21 b11 b21
                                            s.PulseSugar.range1 in
                                        return uu___6))))))
      | PulseSugar.Rewrite { PulseSugar.p11 = p1; PulseSugar.p21 = p2;_} ->
          let uu___ = desugar_vprop env p1 in
          op_let_Question uu___
            (fun p11 ->
               let uu___1 = desugar_vprop env p2 in
               op_let_Question uu___1
                 (fun p21 ->
                    let uu___2 =
                      PulseSyntaxWrapper.tm_rewrite p11 p21
                        s.PulseSugar.range1 in
                    return uu___2))
      | PulseSugar.LetBinding uu___ ->
          fail "Terminal let binding" s.PulseSugar.range1
and (desugar_branch :
  env_t ->
    (FStar_Parser_AST.pattern * PulseSugar.stmt) ->
      PulseSyntaxWrapper.branch err)
  =
  fun env ->
    fun br ->
      let uu___ = br in
      match uu___ with
      | (p, e) ->
          let uu___1 = desugar_pat env p in
          op_let_Question uu___1
            (fun uu___2 ->
               match uu___2 with
               | (p1, vs) ->
                   let uu___3 = push_bvs env vs in
                   (match uu___3 with
                    | (env1, bvs) ->
                        let uu___4 = desugar_stmt env1 e in
                        op_let_Question uu___4
                          (fun e1 ->
                             let e2 =
                               let uu___5 =
                                 FStar_Compiler_List.map
                                   (fun v -> v.FStar_Syntax_Syntax.index) bvs in
                               PulseSyntaxWrapper.close_st_term_n e1 uu___5 in
                             return (p1, e2))))
and (desugar_pat :
  env_t ->
    FStar_Parser_AST.pattern ->
      (PulseSyntaxWrapper.pattern * FStar_Ident.ident Prims.list) err)
  =
  fun env ->
    fun p ->
      let r = p.FStar_Parser_AST.prange in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatVar (id, uu___, uu___1) ->
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Ident.string_of_id id in
              PulseSyntaxWrapper.pat_var uu___4 r in
            (uu___3, [id]) in
          return uu___2
      | FStar_Parser_AST.PatWild uu___ ->
          let id = FStar_Ident.mk_ident ("_", r) in
          let uu___1 =
            let uu___2 = PulseSyntaxWrapper.pat_var "_" r in (uu___2, [id]) in
          return uu___1
      | FStar_Parser_AST.PatConst c ->
          let c1 = desugar_const c in
          let uu___ =
            let uu___1 = PulseSyntaxWrapper.pat_constant c1 r in (uu___1, []) in
          return uu___
      | FStar_Parser_AST.PatName lid ->
          let uu___ = desugar_datacon env lid in
          op_let_Question uu___
            (fun fv ->
               let uu___1 =
                 let uu___2 = PulseSyntaxWrapper.pat_cons fv [] r in
                 (uu___2, []) in
               return uu___1)
      | FStar_Parser_AST.PatApp
          ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName lid;
             FStar_Parser_AST.prange = uu___;_},
           args)
          ->
          let uu___1 = desugar_datacon env lid in
          op_let_Question uu___1
            (fun fv ->
               let uu___2 =
                 map_err
                   (fun p1 ->
                      match p1.FStar_Parser_AST.pat with
                      | FStar_Parser_AST.PatVar (id, uu___3, uu___4) ->
                          return id
                      | FStar_Parser_AST.PatWild uu___3 ->
                          let uu___4 = FStar_Ident.mk_ident ("_", r) in
                          return uu___4
                      | uu___3 ->
                          fail "invalid pattern: no deep patterns allowed" r)
                   args in
               op_let_Question uu___2
                 (fun idents ->
                    let strs =
                      FStar_Compiler_List.map FStar_Ident.string_of_id idents in
                    let pats =
                      FStar_Compiler_List.map
                        (fun s -> PulseSyntaxWrapper.pat_var s r) strs in
                    let uu___3 =
                      let uu___4 = PulseSyntaxWrapper.pat_cons fv pats r in
                      (uu___4, idents) in
                    return uu___3))
      | uu___ -> fail "invalid pattern" r
and (desugar_bind :
  env_t ->
    PulseSugar.stmt'__LetBinding__payload ->
      PulseSugar.stmt ->
        FStar_Compiler_Range_Type.range -> PulseSyntaxWrapper.st_term err)
  =
  fun env ->
    fun lb ->
      fun s2 ->
        fun r ->
          let uu___ = desugar_term_opt env lb.PulseSugar.typ in
          op_let_Question uu___
            (fun annot ->
               let uu___1 =
                 let uu___2 = push_bv env lb.PulseSugar.id in
                 match uu___2 with
                 | (env1, bv) ->
                     let uu___3 = desugar_stmt env1 s2 in
                     op_let_Question uu___3
                       (fun s21 ->
                          let uu___4 =
                            PulseSyntaxWrapper.close_st_term s21
                              bv.FStar_Syntax_Syntax.index in
                          return uu___4) in
               op_let_Question uu___1
                 (fun s21 ->
                    match lb.PulseSugar.init with
                    | FStar_Pervasives_Native.None ->
                        failwith
                          "Uninitialized variables are not yet handled"
                    | FStar_Pervasives_Native.Some e1 ->
                        (match lb.PulseSugar.qualifier with
                         | FStar_Pervasives_Native.None ->
                             let uu___2 = tosyntax env e1 in
                             op_let_Question uu___2
                               (fun s1 ->
                                  let b =
                                    PulseSyntaxWrapper.mk_binder
                                      lb.PulseSugar.id annot in
                                  let t =
                                    let uu___3 = stapp_or_return env s1 in
                                    match uu___3 with
                                    | STTerm s11 -> mk_bind b s11 s21 r
                                    | Return s11 ->
                                        let uu___4 = as_term s11 in
                                        mk_totbind b uu___4 s21 r in
                                  return t)
                         | FStar_Pervasives_Native.Some (PulseSugar.MUT) ->
                             let uu___2 = desugar_term env e1 in
                             op_let_Question uu___2
                               (fun e11 ->
                                  let b =
                                    PulseSyntaxWrapper.mk_binder
                                      lb.PulseSugar.id annot in
                                  let uu___3 =
                                    PulseSyntaxWrapper.tm_let_mut b e11 s21 r in
                                  return uu___3)
                         | FStar_Pervasives_Native.Some (PulseSugar.REF) ->
                             let uu___2 = desugar_term env e1 in
                             op_let_Question uu___2
                               (fun e11 ->
                                  let b =
                                    PulseSyntaxWrapper.mk_binder
                                      lb.PulseSugar.id annot in
                                  let uu___3 =
                                    PulseSyntaxWrapper.tm_let_mut b e11 s21 r in
                                  return uu___3))))
and (desugar_sequence :
  env_t ->
    PulseSugar.stmt ->
      PulseSugar.stmt -> PulseSugar.rng -> PulseSyntaxWrapper.st_term err)
  =
  fun env ->
    fun s1 ->
      fun s2 ->
        fun r ->
          let uu___ = desugar_stmt env s1 in
          op_let_Question uu___
            (fun s11 ->
               let uu___1 = desugar_stmt env s2 in
               op_let_Question uu___1
                 (fun s21 ->
                    let annot =
                      let uu___2 = FStar_Ident.id_of_text "_" in
                      let uu___3 = PulseSyntaxWrapper.tm_unknown r in
                      PulseSyntaxWrapper.mk_binder uu___2 uu___3 in
                    let uu___2 = mk_bind annot s11 s21 r in return uu___2))
and (desugar_assert_with_binders :
  env_t ->
    PulseSugar.stmt ->
      PulseSugar.stmt FStar_Pervasives_Native.option ->
        PulseSugar.rng -> PulseSyntaxWrapper.st_term err)
  =
  fun env ->
    fun s1 ->
      fun k ->
        fun r ->
          match s1.PulseSugar.s with
          | PulseSugar.ProofHintWithBinders
              { PulseSugar.hint_type = hint_type; PulseSugar.binders1 = bs;
                PulseSugar.vprop1 = v;_}
              ->
              let uu___ = desugar_binders env bs in
              op_let_Question uu___
                (fun uu___1 ->
                   match uu___1 with
                   | (env1, binders, bvs) ->
                       let vars =
                         FStar_Compiler_List.map
                           (fun bv -> bv.FStar_Syntax_Syntax.index) bvs in
                       let uu___2 = desugar_vprop env1 v in
                       op_let_Question uu___2
                         (fun v1 ->
                            let uu___3 =
                              match k with
                              | FStar_Pervasives_Native.None ->
                                  let uu___4 =
                                    let uu___5 =
                                      PulseSyntaxWrapper.tm_expr
                                        FStar_Syntax_Syntax.unit_const r in
                                    PulseSyntaxWrapper.tm_ghost_return uu___5
                                      r in
                                  return uu___4
                              | FStar_Pervasives_Native.Some s2 ->
                                  desugar_stmt env1 s2 in
                            op_let_Question uu___3
                              (fun s2 ->
                                 let binders1 =
                                   FStar_Compiler_List.map
                                     FStar_Pervasives_Native.snd binders in
                                 let sub =
                                   PulseSyntaxWrapper.bvs_as_subst vars in
                                 let s21 =
                                   PulseSyntaxWrapper.subst_st_term sub s2 in
                                 let v2 =
                                   PulseSyntaxWrapper.subst_term sub v1 in
                                 let uu___4 =
                                   resolve_hint_type env1 hint_type in
                                 op_let_Question uu___4
                                   (fun ht ->
                                      let uu___5 =
                                        let uu___6 =
                                          PulseSyntaxWrapper.close_binders
                                            binders1 vars in
                                        PulseSyntaxWrapper.tm_proof_hint_with_binders
                                          ht uu___6 v2 s21 r in
                                      return uu___5))))
          | uu___ ->
              fail "Expected ProofHintWithBinders" s1.PulseSugar.range1
and (desugar_binders :
  env_t ->
    PulseSugar.binders ->
      (env_t * (PulseSyntaxWrapper.qualifier FStar_Pervasives_Native.option *
        PulseSyntaxWrapper.binder) Prims.list * FStar_Syntax_Syntax.bv
        Prims.list) err)
  =
  fun env ->
    fun bs ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> return (env1, [], [])
        | (aq, b, t)::bs2 ->
            let uu___ = desugar_term env1 t in
            op_let_Question uu___
              (fun t1 ->
                 let uu___1 = push_bv env1 b in
                 match uu___1 with
                 | (env2, bv) ->
                     let uu___2 = aux env2 bs2 in
                     op_let_Question uu___2
                       (fun uu___3 ->
                          match uu___3 with
                          | (env3, bs3, bvs) ->
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 = as_qual aq in
                                    (uu___7, b, t1) in
                                  uu___6 :: bs3 in
                                (env3, uu___5, (bv :: bvs)) in
                              return uu___4)) in
      let uu___ = aux env bs in
      op_let_Question uu___
        (fun uu___1 ->
           match uu___1 with
           | (env1, bs1, bvs) ->
               let uu___2 =
                 let uu___3 =
                   FStar_Compiler_List.map
                     (fun uu___4 ->
                        match uu___4 with
                        | (aq, b, t) ->
                            let uu___5 = PulseSyntaxWrapper.mk_binder b t in
                            (aq, uu___5)) bs1 in
                 (env1, uu___3, bvs) in
               return uu___2)
and (desugar_computation_type :
  env_t -> PulseSugar.computation_type -> PulseSyntaxWrapper.comp err) =
  fun env ->
    fun c ->
      let uu___ = desugar_vprop env c.PulseSugar.precondition in
      op_let_Question uu___
        (fun pre ->
           let uu___1 = desugar_term env c.PulseSugar.return_type in
           op_let_Question uu___1
             (fun ret1 ->
                let uu___2 = push_bv env c.PulseSugar.return_name in
                match uu___2 with
                | (env1, bv) ->
                    let uu___3 =
                      desugar_vprop env1 c.PulseSugar.postcondition in
                    op_let_Question uu___3
                      (fun post ->
                         let post1 =
                           PulseSyntaxWrapper.close_term post
                             bv.FStar_Syntax_Syntax.index in
                         match c.PulseSugar.tag with
                         | PulseSugar.ST ->
                             let uu___4 =
                               let uu___5 =
                                 PulseSyntaxWrapper.mk_binder
                                   c.PulseSugar.return_name ret1 in
                               PulseSyntaxWrapper.mk_comp pre uu___5 post1 in
                             return uu___4
                         | PulseSugar.STAtomic uu___4 ->
                             let inames = PulseSyntaxWrapper.tm_emp_inames in
                             let uu___5 =
                               let uu___6 =
                                 PulseSyntaxWrapper.mk_binder
                                   c.PulseSugar.return_name ret1 in
                               PulseSyntaxWrapper.atomic_comp inames pre
                                 uu___6 post1 in
                             return uu___5
                         | PulseSugar.STGhost uu___4 ->
                             let inames = PulseSyntaxWrapper.tm_emp_inames in
                             let uu___5 =
                               let uu___6 =
                                 PulseSyntaxWrapper.mk_binder
                                   c.PulseSugar.return_name ret1 in
                               PulseSyntaxWrapper.ghost_comp inames pre
                                 uu___6 post1 in
                             return uu___5)))
let (desugar_decl :
  env_t -> PulseSugar.decl -> PulseSyntaxWrapper.st_term err) =
  fun env ->
    fun p ->
      let uu___ = desugar_binders env p.PulseSugar.binders2 in
      op_let_Question uu___
        (fun uu___1 ->
           match uu___1 with
           | (env1, bs, bvs) ->
               let uu___2 = desugar_stmt env1 p.PulseSugar.body2 in
               op_let_Question uu___2
                 (fun body ->
                    let uu___3 =
                      desugar_computation_type env1 p.PulseSugar.ascription in
                    op_let_Question uu___3
                      (fun comp ->
                         let rec aux bs1 bvs1 =
                           match (bs1, bvs1) with
                           | ((q, last)::[], last_bv::[]) ->
                               let body1 =
                                 PulseSyntaxWrapper.close_st_term body
                                   last_bv.FStar_Syntax_Syntax.index in
                               let comp1 =
                                 PulseSyntaxWrapper.close_comp comp
                                   last_bv.FStar_Syntax_Syntax.index in
                               let uu___4 =
                                 PulseSyntaxWrapper.tm_abs last q comp1 body1
                                   p.PulseSugar.range2 in
                               return uu___4
                           | ((q, b)::bs2, bv::bvs2) ->
                               let uu___4 = aux bs2 bvs2 in
                               op_let_Question uu___4
                                 (fun body1 ->
                                    let body2 =
                                      PulseSyntaxWrapper.close_st_term body1
                                        bv.FStar_Syntax_Syntax.index in
                                    let comp1 =
                                      let uu___5 =
                                        PulseSyntaxWrapper.tm_unknown r_ in
                                      PulseSyntaxWrapper.mk_tot uu___5 in
                                    let uu___5 =
                                      PulseSyntaxWrapper.tm_abs b q comp1
                                        body2 p.PulseSugar.range2 in
                                    return uu___5)
                           | uu___4 ->
                               fail "Unexpected empty binders in decl" r_ in
                         aux bs bvs)))
type name = Prims.string Prims.list
let (initialize_env :
  FStar_TypeChecker_Env.env ->
    name Prims.list -> (Prims.string * name) Prims.list -> env_t)
  =
  fun env ->
    fun open_namespaces ->
      fun module_abbrevs ->
        let dsenv = env.FStar_TypeChecker_Env.dsenv in
        let dsenv1 =
          let uu___ = FStar_TypeChecker_Env.current_module env in
          FStar_Syntax_DsEnv.set_current_module dsenv uu___ in
        let dsenv2 =
          FStar_Compiler_List.fold_right
            (fun ns ->
               fun env1 ->
                 let uu___ = FStar_Ident.lid_of_path ns r_ in
                 FStar_Syntax_DsEnv.push_namespace env1 uu___)
            open_namespaces dsenv1 in
        let dsenv3 =
          let uu___ = FStar_TypeChecker_Env.current_module env in
          FStar_Syntax_DsEnv.push_namespace dsenv2 uu___ in
        let dsenv4 =
          FStar_Compiler_List.fold_left
            (fun env1 ->
               fun uu___ ->
                 match uu___ with
                 | (m, n) ->
                     let uu___1 = FStar_Ident.id_of_text m in
                     let uu___2 = FStar_Ident.lid_of_path n r_ in
                     FStar_Syntax_DsEnv.push_module_abbrev env1 uu___1 uu___2)
            dsenv3 module_abbrevs in
        let env1 =
          {
            FStar_TypeChecker_Env.solver = (env.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (env.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma = (env.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (env.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (env.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (env.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (env.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab = (env.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (env.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (env.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (env.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (env.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (env.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (env.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (env.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq_strict =
              (env.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (env.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (env.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 = (env.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (env.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (env.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (env.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.intactics =
              (env.FStar_TypeChecker_Env.intactics);
            FStar_TypeChecker_Env.tc_term =
              (env.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStar_TypeChecker_Env.universe_of =
              (env.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStar_TypeChecker_Env.teq_nosmt_force =
              (env.FStar_TypeChecker_Env.teq_nosmt_force);
            FStar_TypeChecker_Env.subtype_nosmt_force =
              (env.FStar_TypeChecker_Env.subtype_nosmt_force);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (env.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (env.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (env.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (env.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (env.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice = (env.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (env.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (env.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (env.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (env.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv = dsenv4;
            FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (env.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (env.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (env.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
            FStar_TypeChecker_Env.erase_erasable_args =
              (env.FStar_TypeChecker_Env.erase_erasable_args);
            FStar_TypeChecker_Env.core_check =
              (env.FStar_TypeChecker_Env.core_check)
          } in
        { tcenv = env1; local_refs = [] }