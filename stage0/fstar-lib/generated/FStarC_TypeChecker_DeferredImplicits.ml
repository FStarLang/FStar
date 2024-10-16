open Prims
let (is_flex : FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStarC_Syntax_Util.head_and_args_full t in
    match uu___ with
    | (head, _args) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress head in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_uvar uu___2 -> true
         | uu___2 -> false)
let (flex_uvar_head :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.ctx_uvar) =
  fun t ->
    let uu___ = FStarC_Syntax_Util.head_and_args_full t in
    match uu___ with
    | (head, _args) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress head in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_uvar (u, uu___2) -> u
         | uu___2 -> failwith "Not a flex-uvar")
type goal_type =
  | FlexRigid of (FStarC_Syntax_Syntax.ctx_uvar * FStarC_Syntax_Syntax.term)
  
  | FlexFlex of (FStarC_Syntax_Syntax.ctx_uvar *
  FStarC_Syntax_Syntax.ctx_uvar) 
  | Can_be_split_into of (FStarC_Syntax_Syntax.term *
  FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.ctx_uvar) 
  | Imp of FStarC_Syntax_Syntax.ctx_uvar 
let (uu___is_FlexRigid : goal_type -> Prims.bool) =
  fun projectee ->
    match projectee with | FlexRigid _0 -> true | uu___ -> false
let (__proj__FlexRigid__item___0 :
  goal_type -> (FStarC_Syntax_Syntax.ctx_uvar * FStarC_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | FlexRigid _0 -> _0
let (uu___is_FlexFlex : goal_type -> Prims.bool) =
  fun projectee ->
    match projectee with | FlexFlex _0 -> true | uu___ -> false
let (__proj__FlexFlex__item___0 :
  goal_type ->
    (FStarC_Syntax_Syntax.ctx_uvar * FStarC_Syntax_Syntax.ctx_uvar))
  = fun projectee -> match projectee with | FlexFlex _0 -> _0
let (uu___is_Can_be_split_into : goal_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Can_be_split_into _0 -> true | uu___ -> false
let (__proj__Can_be_split_into__item___0 :
  goal_type ->
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term *
      FStarC_Syntax_Syntax.ctx_uvar))
  = fun projectee -> match projectee with | Can_be_split_into _0 -> _0
let (uu___is_Imp : goal_type -> Prims.bool) =
  fun projectee -> match projectee with | Imp _0 -> true | uu___ -> false
let (__proj__Imp__item___0 : goal_type -> FStarC_Syntax_Syntax.ctx_uvar) =
  fun projectee -> match projectee with | Imp _0 -> _0
let (find_user_tac_for_uvar :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Syntax.ctx_uvar ->
      FStarC_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env ->
    fun u ->
      let rec attr_list_elements e =
        let uu___ =
          let uu___1 = FStarC_Syntax_Util.unmeta e in
          FStarC_Syntax_Util.head_and_args uu___1 in
        match uu___ with
        | (head, args) ->
            let uu___1 =
              let uu___2 =
                let uu___3 = FStarC_Syntax_Util.un_uinst head in
                uu___3.FStarC_Syntax_Syntax.n in
              (uu___2, args) in
            (match uu___1 with
             | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___2) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.nil_lid
                 -> FStar_Pervasives_Native.Some []
             | (FStarC_Syntax_Syntax.Tm_fvar fv,
                uu___2::(hd, uu___3)::(tl, uu___4)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.cons_lid
                 ->
                 (match hd.FStarC_Syntax_Syntax.n with
                  | FStarC_Syntax_Syntax.Tm_constant
                      (FStarC_Const.Const_string (s, uu___5)) ->
                      let uu___6 = attr_list_elements tl in
                      (match uu___6 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some tl1 ->
                           FStar_Pervasives_Native.Some (s :: tl1))
                  | uu___5 -> FStar_Pervasives_Native.None)
             | (FStarC_Syntax_Syntax.Tm_fvar fv,
                (hd, uu___2)::(tl, uu___3)::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fv
                   FStarC_Parser_Const.cons_lid
                 ->
                 (match hd.FStarC_Syntax_Syntax.n with
                  | FStarC_Syntax_Syntax.Tm_constant
                      (FStarC_Const.Const_string (s, uu___4)) ->
                      let uu___5 = attr_list_elements tl in
                      (match uu___5 with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.None
                       | FStar_Pervasives_Native.Some tl1 ->
                           FStar_Pervasives_Native.Some (s :: tl1))
                  | uu___4 -> FStar_Pervasives_Native.None)
             | uu___2 -> FStar_Pervasives_Native.None) in
      let candidate_names candidates =
        let uu___ =
          let uu___1 =
            FStarC_Compiler_List.collect FStarC_Syntax_Util.lids_of_sigelt
              candidates in
          FStarC_Compiler_List.map FStarC_Ident.string_of_lid uu___1 in
        FStarC_Compiler_String.concat ", " uu___ in
      match u.FStarC_Syntax_Syntax.ctx_uvar_meta with
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Ctx_uvar_meta_attr
          a) ->
          let hooks =
            FStarC_TypeChecker_Env.lookup_attr env
              FStarC_Parser_Const.resolve_implicits_attr_string in
          let candidates =
            FStarC_Compiler_List.filter
              (fun hook ->
                 FStarC_Compiler_Util.for_some
                   (FStarC_TypeChecker_TermEqAndSimplify.eq_tm_bool env a)
                   hook.FStarC_Syntax_Syntax.sigattrs) hooks in
          let candidates1 =
            FStarC_Compiler_Util.remove_dups
              (fun s0 ->
                 fun s1 ->
                   let l0 = FStarC_Syntax_Util.lids_of_sigelt s0 in
                   let l1 = FStarC_Syntax_Util.lids_of_sigelt s1 in
                   if
                     (FStarC_Compiler_List.length l0) =
                       (FStarC_Compiler_List.length l1)
                   then
                     FStarC_Compiler_List.forall2
                       (fun l01 -> fun l11 -> FStarC_Ident.lid_equals l01 l11)
                       l0 l1
                   else false) candidates in
          let is_overridden candidate =
            let candidate_lids = FStarC_Syntax_Util.lids_of_sigelt candidate in
            FStarC_Compiler_Util.for_some
              (fun other ->
                 FStarC_Compiler_Util.for_some
                   (fun attr ->
                      let uu___ = FStarC_Syntax_Util.head_and_args attr in
                      match uu___ with
                      | (head, args) ->
                          let uu___1 =
                            let uu___2 =
                              let uu___3 = FStarC_Syntax_Util.un_uinst head in
                              uu___3.FStarC_Syntax_Syntax.n in
                            (uu___2, args) in
                          (match uu___1 with
                           | (FStarC_Syntax_Syntax.Tm_fvar fv,
                              uu___2::(a', uu___3)::(overrides, uu___4)::[])
                               when
                               (FStarC_Syntax_Syntax.fv_eq_lid fv
                                  FStarC_Parser_Const.override_resolve_implicits_handler_lid)
                                 &&
                                 (FStarC_TypeChecker_TermEqAndSimplify.eq_tm_bool
                                    env a a')
                               ->
                               let uu___5 = attr_list_elements overrides in
                               (match uu___5 with
                                | FStar_Pervasives_Native.None -> false
                                | FStar_Pervasives_Native.Some names ->
                                    FStarC_Compiler_Util.for_some
                                      (fun n ->
                                         FStarC_Compiler_Util.for_some
                                           (fun l ->
                                              let uu___6 =
                                                FStarC_Ident.string_of_lid l in
                                              uu___6 = n) candidate_lids)
                                      names)
                           | (FStarC_Syntax_Syntax.Tm_fvar fv,
                              (a', uu___2)::(overrides, uu___3)::[]) when
                               (FStarC_Syntax_Syntax.fv_eq_lid fv
                                  FStarC_Parser_Const.override_resolve_implicits_handler_lid)
                                 &&
                                 (FStarC_TypeChecker_TermEqAndSimplify.eq_tm_bool
                                    env a a')
                               ->
                               let uu___4 = attr_list_elements overrides in
                               (match uu___4 with
                                | FStar_Pervasives_Native.None -> false
                                | FStar_Pervasives_Native.Some names ->
                                    FStarC_Compiler_Util.for_some
                                      (fun n ->
                                         FStarC_Compiler_Util.for_some
                                           (fun l ->
                                              let uu___5 =
                                                FStarC_Ident.string_of_lid l in
                                              uu___5 = n) candidate_lids)
                                      names)
                           | uu___2 -> false))
                   other.FStarC_Syntax_Syntax.sigattrs) candidates1 in
          let candidates2 =
            FStarC_Compiler_List.filter
              (fun c ->
                 let uu___ = is_overridden c in Prims.op_Negation uu___)
              candidates1 in
          (match candidates2 with
           | [] -> FStar_Pervasives_Native.None
           | c::[] -> FStar_Pervasives_Native.Some c
           | uu___ ->
               let candidates3 = candidate_names candidates2 in
               let attr =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term a in
               ((let uu___2 =
                   FStarC_Compiler_Util.format2
                     "Multiple resolve_implicits hooks are eligible for attribute %s; \nplease resolve the ambiguity by using the `override_resolve_implicits_handler` attribute to choose among these candidates {%s}"
                     attr candidates3 in
                 FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range
                   u.FStarC_Syntax_Syntax.ctx_uvar_range
                   FStarC_Errors_Codes.Warning_AmbiguousResolveImplicitsHook
                   () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic uu___2));
                FStar_Pervasives_Native.None))
      | uu___ -> FStar_Pervasives_Native.None
let (should_defer_uvar_to_user_tac :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.ctx_uvar -> Prims.bool)
  =
  fun env ->
    fun u ->
      if Prims.op_Negation env.FStarC_TypeChecker_Env.enable_defer_to_tac
      then false
      else
        (let uu___1 = find_user_tac_for_uvar env u in
         FStar_Pervasives_Native.uu___is_Some uu___1)
let solve_goals_with_tac :
  'uuuuu .
    FStarC_TypeChecker_Env.env ->
      'uuuuu ->
        FStarC_TypeChecker_Common.implicits ->
          FStarC_Syntax_Syntax.sigelt -> unit
  =
  fun env ->
    fun g ->
      fun deferred_goals ->
        fun tac ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_TypeChecker_Env.current_module env in
              FStarC_Ident.string_of_lid uu___2 in
            FStar_Pervasives_Native.Some uu___1 in
          FStarC_Profiling.profile
            (fun uu___1 ->
               let resolve_tac =
                 match tac.FStarC_Syntax_Syntax.sigel with
                 | FStarC_Syntax_Syntax.Sig_let
                     { FStarC_Syntax_Syntax.lbs1 = uu___2;
                       FStarC_Syntax_Syntax.lids1 = lid::[];_}
                     ->
                     let qn = FStarC_TypeChecker_Env.lookup_qname env lid in
                     let fv =
                       FStarC_Syntax_Syntax.lid_as_fv lid
                         FStar_Pervasives_Native.None in
                     let term =
                       let uu___3 =
                         FStarC_Syntax_Syntax.lid_as_fv lid
                           FStar_Pervasives_Native.None in
                       FStarC_Syntax_Syntax.fv_to_tm uu___3 in
                     term
                 | uu___2 -> failwith "Resolve_tac not found" in
               let env1 =
                 {
                   FStarC_TypeChecker_Env.solver =
                     (env.FStarC_TypeChecker_Env.solver);
                   FStarC_TypeChecker_Env.range =
                     (env.FStarC_TypeChecker_Env.range);
                   FStarC_TypeChecker_Env.curmodule =
                     (env.FStarC_TypeChecker_Env.curmodule);
                   FStarC_TypeChecker_Env.gamma =
                     (env.FStarC_TypeChecker_Env.gamma);
                   FStarC_TypeChecker_Env.gamma_sig =
                     (env.FStarC_TypeChecker_Env.gamma_sig);
                   FStarC_TypeChecker_Env.gamma_cache =
                     (env.FStarC_TypeChecker_Env.gamma_cache);
                   FStarC_TypeChecker_Env.modules =
                     (env.FStarC_TypeChecker_Env.modules);
                   FStarC_TypeChecker_Env.expected_typ =
                     (env.FStarC_TypeChecker_Env.expected_typ);
                   FStarC_TypeChecker_Env.sigtab =
                     (env.FStarC_TypeChecker_Env.sigtab);
                   FStarC_TypeChecker_Env.attrtab =
                     (env.FStarC_TypeChecker_Env.attrtab);
                   FStarC_TypeChecker_Env.instantiate_imp =
                     (env.FStarC_TypeChecker_Env.instantiate_imp);
                   FStarC_TypeChecker_Env.effects =
                     (env.FStarC_TypeChecker_Env.effects);
                   FStarC_TypeChecker_Env.generalize =
                     (env.FStarC_TypeChecker_Env.generalize);
                   FStarC_TypeChecker_Env.letrecs =
                     (env.FStarC_TypeChecker_Env.letrecs);
                   FStarC_TypeChecker_Env.top_level =
                     (env.FStarC_TypeChecker_Env.top_level);
                   FStarC_TypeChecker_Env.check_uvars =
                     (env.FStarC_TypeChecker_Env.check_uvars);
                   FStarC_TypeChecker_Env.use_eq_strict =
                     (env.FStarC_TypeChecker_Env.use_eq_strict);
                   FStarC_TypeChecker_Env.is_iface =
                     (env.FStarC_TypeChecker_Env.is_iface);
                   FStarC_TypeChecker_Env.admit =
                     (env.FStarC_TypeChecker_Env.admit);
                   FStarC_TypeChecker_Env.lax_universes =
                     (env.FStarC_TypeChecker_Env.lax_universes);
                   FStarC_TypeChecker_Env.phase1 =
                     (env.FStarC_TypeChecker_Env.phase1);
                   FStarC_TypeChecker_Env.failhard =
                     (env.FStarC_TypeChecker_Env.failhard);
                   FStarC_TypeChecker_Env.flychecking =
                     (env.FStarC_TypeChecker_Env.flychecking);
                   FStarC_TypeChecker_Env.uvar_subtyping =
                     (env.FStarC_TypeChecker_Env.uvar_subtyping);
                   FStarC_TypeChecker_Env.intactics =
                     (env.FStarC_TypeChecker_Env.intactics);
                   FStarC_TypeChecker_Env.nocoerce =
                     (env.FStarC_TypeChecker_Env.nocoerce);
                   FStarC_TypeChecker_Env.tc_term =
                     (env.FStarC_TypeChecker_Env.tc_term);
                   FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                     (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                   FStarC_TypeChecker_Env.universe_of =
                     (env.FStarC_TypeChecker_Env.universe_of);
                   FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                     =
                     (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                   FStarC_TypeChecker_Env.teq_nosmt_force =
                     (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                   FStarC_TypeChecker_Env.subtype_nosmt_force =
                     (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                   FStarC_TypeChecker_Env.qtbl_name_and_index =
                     (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                   FStarC_TypeChecker_Env.normalized_eff_names =
                     (env.FStarC_TypeChecker_Env.normalized_eff_names);
                   FStarC_TypeChecker_Env.fv_delta_depths =
                     (env.FStarC_TypeChecker_Env.fv_delta_depths);
                   FStarC_TypeChecker_Env.proof_ns =
                     (env.FStarC_TypeChecker_Env.proof_ns);
                   FStarC_TypeChecker_Env.synth_hook =
                     (env.FStarC_TypeChecker_Env.synth_hook);
                   FStarC_TypeChecker_Env.try_solve_implicits_hook =
                     (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                   FStarC_TypeChecker_Env.splice =
                     (env.FStarC_TypeChecker_Env.splice);
                   FStarC_TypeChecker_Env.mpreprocess =
                     (env.FStarC_TypeChecker_Env.mpreprocess);
                   FStarC_TypeChecker_Env.postprocess =
                     (env.FStarC_TypeChecker_Env.postprocess);
                   FStarC_TypeChecker_Env.identifier_info =
                     (env.FStarC_TypeChecker_Env.identifier_info);
                   FStarC_TypeChecker_Env.tc_hooks =
                     (env.FStarC_TypeChecker_Env.tc_hooks);
                   FStarC_TypeChecker_Env.dsenv =
                     (env.FStarC_TypeChecker_Env.dsenv);
                   FStarC_TypeChecker_Env.nbe =
                     (env.FStarC_TypeChecker_Env.nbe);
                   FStarC_TypeChecker_Env.strict_args_tab =
                     (env.FStarC_TypeChecker_Env.strict_args_tab);
                   FStarC_TypeChecker_Env.erasable_types_tab =
                     (env.FStarC_TypeChecker_Env.erasable_types_tab);
                   FStarC_TypeChecker_Env.enable_defer_to_tac = false;
                   FStarC_TypeChecker_Env.unif_allow_ref_guards =
                     (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                   FStarC_TypeChecker_Env.erase_erasable_args =
                     (env.FStarC_TypeChecker_Env.erase_erasable_args);
                   FStarC_TypeChecker_Env.core_check =
                     (env.FStarC_TypeChecker_Env.core_check);
                   FStarC_TypeChecker_Env.missing_decl =
                     (env.FStarC_TypeChecker_Env.missing_decl)
                 } in
               env1.FStarC_TypeChecker_Env.try_solve_implicits_hook env1
                 resolve_tac deferred_goals) uu___
            "FStarC.TypeChecker.DeferredImplicits.solve_goals_with_tac"
let (solve_deferred_to_tactic_goals :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.guard_t -> FStarC_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      if Prims.op_Negation env.FStarC_TypeChecker_Env.enable_defer_to_tac
      then g
      else
        (let deferred = g.FStarC_TypeChecker_Common.deferred_to_tac in
         let prob_as_implicit uu___1 =
           match uu___1 with
           | (uu___2, reason, prob) ->
               (match prob with
                | FStarC_TypeChecker_Common.TProb tp when
                    tp.FStarC_TypeChecker_Common.relation =
                      FStarC_TypeChecker_Common.EQ
                    ->
                    let uu___3 =
                      FStarC_TypeChecker_Env.clear_expected_typ env in
                    (match uu___3 with
                     | (env1, uu___4) ->
                         let env2 =
                           {
                             FStarC_TypeChecker_Env.solver =
                               (env1.FStarC_TypeChecker_Env.solver);
                             FStarC_TypeChecker_Env.range =
                               (env1.FStarC_TypeChecker_Env.range);
                             FStarC_TypeChecker_Env.curmodule =
                               (env1.FStarC_TypeChecker_Env.curmodule);
                             FStarC_TypeChecker_Env.gamma =
                               ((tp.FStarC_TypeChecker_Common.logical_guard_uvar).FStarC_Syntax_Syntax.ctx_uvar_gamma);
                             FStarC_TypeChecker_Env.gamma_sig =
                               (env1.FStarC_TypeChecker_Env.gamma_sig);
                             FStarC_TypeChecker_Env.gamma_cache =
                               (env1.FStarC_TypeChecker_Env.gamma_cache);
                             FStarC_TypeChecker_Env.modules =
                               (env1.FStarC_TypeChecker_Env.modules);
                             FStarC_TypeChecker_Env.expected_typ =
                               (env1.FStarC_TypeChecker_Env.expected_typ);
                             FStarC_TypeChecker_Env.sigtab =
                               (env1.FStarC_TypeChecker_Env.sigtab);
                             FStarC_TypeChecker_Env.attrtab =
                               (env1.FStarC_TypeChecker_Env.attrtab);
                             FStarC_TypeChecker_Env.instantiate_imp =
                               (env1.FStarC_TypeChecker_Env.instantiate_imp);
                             FStarC_TypeChecker_Env.effects =
                               (env1.FStarC_TypeChecker_Env.effects);
                             FStarC_TypeChecker_Env.generalize =
                               (env1.FStarC_TypeChecker_Env.generalize);
                             FStarC_TypeChecker_Env.letrecs =
                               (env1.FStarC_TypeChecker_Env.letrecs);
                             FStarC_TypeChecker_Env.top_level =
                               (env1.FStarC_TypeChecker_Env.top_level);
                             FStarC_TypeChecker_Env.check_uvars =
                               (env1.FStarC_TypeChecker_Env.check_uvars);
                             FStarC_TypeChecker_Env.use_eq_strict =
                               (env1.FStarC_TypeChecker_Env.use_eq_strict);
                             FStarC_TypeChecker_Env.is_iface =
                               (env1.FStarC_TypeChecker_Env.is_iface);
                             FStarC_TypeChecker_Env.admit =
                               (env1.FStarC_TypeChecker_Env.admit);
                             FStarC_TypeChecker_Env.lax_universes =
                               (env1.FStarC_TypeChecker_Env.lax_universes);
                             FStarC_TypeChecker_Env.phase1 =
                               (env1.FStarC_TypeChecker_Env.phase1);
                             FStarC_TypeChecker_Env.failhard =
                               (env1.FStarC_TypeChecker_Env.failhard);
                             FStarC_TypeChecker_Env.flychecking =
                               (env1.FStarC_TypeChecker_Env.flychecking);
                             FStarC_TypeChecker_Env.uvar_subtyping =
                               (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                             FStarC_TypeChecker_Env.intactics =
                               (env1.FStarC_TypeChecker_Env.intactics);
                             FStarC_TypeChecker_Env.nocoerce =
                               (env1.FStarC_TypeChecker_Env.nocoerce);
                             FStarC_TypeChecker_Env.tc_term =
                               (env1.FStarC_TypeChecker_Env.tc_term);
                             FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                               (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                             FStarC_TypeChecker_Env.universe_of =
                               (env1.FStarC_TypeChecker_Env.universe_of);
                             FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                               =
                               (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                             FStarC_TypeChecker_Env.teq_nosmt_force =
                               (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                             FStarC_TypeChecker_Env.subtype_nosmt_force =
                               (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                             FStarC_TypeChecker_Env.qtbl_name_and_index =
                               (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                             FStarC_TypeChecker_Env.normalized_eff_names =
                               (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                             FStarC_TypeChecker_Env.fv_delta_depths =
                               (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                             FStarC_TypeChecker_Env.proof_ns =
                               (env1.FStarC_TypeChecker_Env.proof_ns);
                             FStarC_TypeChecker_Env.synth_hook =
                               (env1.FStarC_TypeChecker_Env.synth_hook);
                             FStarC_TypeChecker_Env.try_solve_implicits_hook
                               =
                               (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                             FStarC_TypeChecker_Env.splice =
                               (env1.FStarC_TypeChecker_Env.splice);
                             FStarC_TypeChecker_Env.mpreprocess =
                               (env1.FStarC_TypeChecker_Env.mpreprocess);
                             FStarC_TypeChecker_Env.postprocess =
                               (env1.FStarC_TypeChecker_Env.postprocess);
                             FStarC_TypeChecker_Env.identifier_info =
                               (env1.FStarC_TypeChecker_Env.identifier_info);
                             FStarC_TypeChecker_Env.tc_hooks =
                               (env1.FStarC_TypeChecker_Env.tc_hooks);
                             FStarC_TypeChecker_Env.dsenv =
                               (env1.FStarC_TypeChecker_Env.dsenv);
                             FStarC_TypeChecker_Env.nbe =
                               (env1.FStarC_TypeChecker_Env.nbe);
                             FStarC_TypeChecker_Env.strict_args_tab =
                               (env1.FStarC_TypeChecker_Env.strict_args_tab);
                             FStarC_TypeChecker_Env.erasable_types_tab =
                               (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                             FStarC_TypeChecker_Env.enable_defer_to_tac =
                               (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                             FStarC_TypeChecker_Env.unif_allow_ref_guards =
                               (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                             FStarC_TypeChecker_Env.erase_erasable_args =
                               (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                             FStarC_TypeChecker_Env.core_check =
                               (env1.FStarC_TypeChecker_Env.core_check);
                             FStarC_TypeChecker_Env.missing_decl =
                               (env1.FStarC_TypeChecker_Env.missing_decl)
                           } in
                         let env_lax =
                           {
                             FStarC_TypeChecker_Env.solver =
                               (env2.FStarC_TypeChecker_Env.solver);
                             FStarC_TypeChecker_Env.range =
                               (env2.FStarC_TypeChecker_Env.range);
                             FStarC_TypeChecker_Env.curmodule =
                               (env2.FStarC_TypeChecker_Env.curmodule);
                             FStarC_TypeChecker_Env.gamma =
                               (env2.FStarC_TypeChecker_Env.gamma);
                             FStarC_TypeChecker_Env.gamma_sig =
                               (env2.FStarC_TypeChecker_Env.gamma_sig);
                             FStarC_TypeChecker_Env.gamma_cache =
                               (env2.FStarC_TypeChecker_Env.gamma_cache);
                             FStarC_TypeChecker_Env.modules =
                               (env2.FStarC_TypeChecker_Env.modules);
                             FStarC_TypeChecker_Env.expected_typ =
                               (env2.FStarC_TypeChecker_Env.expected_typ);
                             FStarC_TypeChecker_Env.sigtab =
                               (env2.FStarC_TypeChecker_Env.sigtab);
                             FStarC_TypeChecker_Env.attrtab =
                               (env2.FStarC_TypeChecker_Env.attrtab);
                             FStarC_TypeChecker_Env.instantiate_imp =
                               (env2.FStarC_TypeChecker_Env.instantiate_imp);
                             FStarC_TypeChecker_Env.effects =
                               (env2.FStarC_TypeChecker_Env.effects);
                             FStarC_TypeChecker_Env.generalize =
                               (env2.FStarC_TypeChecker_Env.generalize);
                             FStarC_TypeChecker_Env.letrecs =
                               (env2.FStarC_TypeChecker_Env.letrecs);
                             FStarC_TypeChecker_Env.top_level =
                               (env2.FStarC_TypeChecker_Env.top_level);
                             FStarC_TypeChecker_Env.check_uvars =
                               (env2.FStarC_TypeChecker_Env.check_uvars);
                             FStarC_TypeChecker_Env.use_eq_strict =
                               (env2.FStarC_TypeChecker_Env.use_eq_strict);
                             FStarC_TypeChecker_Env.is_iface =
                               (env2.FStarC_TypeChecker_Env.is_iface);
                             FStarC_TypeChecker_Env.admit = true;
                             FStarC_TypeChecker_Env.lax_universes =
                               (env2.FStarC_TypeChecker_Env.lax_universes);
                             FStarC_TypeChecker_Env.phase1 =
                               (env2.FStarC_TypeChecker_Env.phase1);
                             FStarC_TypeChecker_Env.failhard =
                               (env2.FStarC_TypeChecker_Env.failhard);
                             FStarC_TypeChecker_Env.flychecking =
                               (env2.FStarC_TypeChecker_Env.flychecking);
                             FStarC_TypeChecker_Env.uvar_subtyping =
                               (env2.FStarC_TypeChecker_Env.uvar_subtyping);
                             FStarC_TypeChecker_Env.intactics =
                               (env2.FStarC_TypeChecker_Env.intactics);
                             FStarC_TypeChecker_Env.nocoerce =
                               (env2.FStarC_TypeChecker_Env.nocoerce);
                             FStarC_TypeChecker_Env.tc_term =
                               (env2.FStarC_TypeChecker_Env.tc_term);
                             FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                               (env2.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                             FStarC_TypeChecker_Env.universe_of =
                               (env2.FStarC_TypeChecker_Env.universe_of);
                             FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                               =
                               (env2.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                             FStarC_TypeChecker_Env.teq_nosmt_force =
                               (env2.FStarC_TypeChecker_Env.teq_nosmt_force);
                             FStarC_TypeChecker_Env.subtype_nosmt_force =
                               (env2.FStarC_TypeChecker_Env.subtype_nosmt_force);
                             FStarC_TypeChecker_Env.qtbl_name_and_index =
                               (env2.FStarC_TypeChecker_Env.qtbl_name_and_index);
                             FStarC_TypeChecker_Env.normalized_eff_names =
                               (env2.FStarC_TypeChecker_Env.normalized_eff_names);
                             FStarC_TypeChecker_Env.fv_delta_depths =
                               (env2.FStarC_TypeChecker_Env.fv_delta_depths);
                             FStarC_TypeChecker_Env.proof_ns =
                               (env2.FStarC_TypeChecker_Env.proof_ns);
                             FStarC_TypeChecker_Env.synth_hook =
                               (env2.FStarC_TypeChecker_Env.synth_hook);
                             FStarC_TypeChecker_Env.try_solve_implicits_hook
                               =
                               (env2.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                             FStarC_TypeChecker_Env.splice =
                               (env2.FStarC_TypeChecker_Env.splice);
                             FStarC_TypeChecker_Env.mpreprocess =
                               (env2.FStarC_TypeChecker_Env.mpreprocess);
                             FStarC_TypeChecker_Env.postprocess =
                               (env2.FStarC_TypeChecker_Env.postprocess);
                             FStarC_TypeChecker_Env.identifier_info =
                               (env2.FStarC_TypeChecker_Env.identifier_info);
                             FStarC_TypeChecker_Env.tc_hooks =
                               (env2.FStarC_TypeChecker_Env.tc_hooks);
                             FStarC_TypeChecker_Env.dsenv =
                               (env2.FStarC_TypeChecker_Env.dsenv);
                             FStarC_TypeChecker_Env.nbe =
                               (env2.FStarC_TypeChecker_Env.nbe);
                             FStarC_TypeChecker_Env.strict_args_tab =
                               (env2.FStarC_TypeChecker_Env.strict_args_tab);
                             FStarC_TypeChecker_Env.erasable_types_tab =
                               (env2.FStarC_TypeChecker_Env.erasable_types_tab);
                             FStarC_TypeChecker_Env.enable_defer_to_tac =
                               false;
                             FStarC_TypeChecker_Env.unif_allow_ref_guards =
                               (env2.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                             FStarC_TypeChecker_Env.erase_erasable_args =
                               (env2.FStarC_TypeChecker_Env.erase_erasable_args);
                             FStarC_TypeChecker_Env.core_check =
                               (env2.FStarC_TypeChecker_Env.core_check);
                             FStarC_TypeChecker_Env.missing_decl =
                               (env2.FStarC_TypeChecker_Env.missing_decl)
                           } in
                         let uu___5 =
                           let t =
                             let uu___6 =
                               is_flex tp.FStarC_TypeChecker_Common.lhs in
                             if uu___6
                             then tp.FStarC_TypeChecker_Common.lhs
                             else tp.FStarC_TypeChecker_Common.rhs in
                           env2.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                             env_lax t true in
                         (match uu___5 with
                          | (uu___6, t_eq, uu___7) ->
                              let goal_ty =
                                let uu___8 =
                                  env2.FStarC_TypeChecker_Env.universe_of
                                    env_lax t_eq in
                                FStarC_Syntax_Util.mk_eq2 uu___8 t_eq
                                  tp.FStarC_TypeChecker_Common.lhs
                                  tp.FStarC_TypeChecker_Common.rhs in
                              let uu___8 =
                                FStarC_TypeChecker_Env.new_implicit_var_aux
                                  reason
                                  (tp.FStarC_TypeChecker_Common.lhs).FStarC_Syntax_Syntax.pos
                                  env2 goal_ty FStarC_Syntax_Syntax.Strict
                                  FStar_Pervasives_Native.None false in
                              (match uu___8 with
                               | (goal, ctx_uvar, uu___9) ->
                                   let imp =
                                     {
                                       FStarC_TypeChecker_Common.imp_reason =
                                         "";
                                       FStarC_TypeChecker_Common.imp_uvar =
                                         (FStar_Pervasives_Native.fst
                                            ctx_uvar);
                                       FStarC_TypeChecker_Common.imp_tm =
                                         goal;
                                       FStarC_TypeChecker_Common.imp_range =
                                         ((tp.FStarC_TypeChecker_Common.lhs).FStarC_Syntax_Syntax.pos)
                                     } in
                                   let sigelt =
                                     let uu___10 =
                                       is_flex
                                         tp.FStarC_TypeChecker_Common.lhs in
                                     if uu___10
                                     then
                                       let uu___11 =
                                         let uu___12 =
                                           flex_uvar_head
                                             tp.FStarC_TypeChecker_Common.lhs in
                                         find_user_tac_for_uvar env2 uu___12 in
                                       match uu___11 with
                                       | FStar_Pervasives_Native.None ->
                                           let uu___12 =
                                             is_flex
                                               tp.FStarC_TypeChecker_Common.rhs in
                                           (if uu___12
                                            then
                                              let uu___13 =
                                                flex_uvar_head
                                                  tp.FStarC_TypeChecker_Common.rhs in
                                              find_user_tac_for_uvar env2
                                                uu___13
                                            else FStar_Pervasives_Native.None)
                                       | v -> v
                                     else
                                       (let uu___12 =
                                          is_flex
                                            tp.FStarC_TypeChecker_Common.rhs in
                                        if uu___12
                                        then
                                          let uu___13 =
                                            flex_uvar_head
                                              tp.FStarC_TypeChecker_Common.rhs in
                                          find_user_tac_for_uvar env2 uu___13
                                        else FStar_Pervasives_Native.None) in
                                   (match sigelt with
                                    | FStar_Pervasives_Native.None ->
                                        failwith
                                          "Impossible: No tactic associated with deferred problem"
                                    | FStar_Pervasives_Native.Some se ->
                                        (imp, se)))))
                | uu___3 -> failwith "Unexpected problem deferred to tactic") in
         let eqs =
           let uu___1 =
             FStarC_Class_Listlike.to_list
               (FStarC_Compiler_CList.listlike_clist ())
               g.FStarC_TypeChecker_Common.deferred_to_tac in
           FStarC_Compiler_List.map prob_as_implicit uu___1 in
         let uu___1 =
           let uu___2 =
             FStarC_Class_Listlike.to_list
               (FStarC_Compiler_CList.listlike_clist ())
               g.FStarC_TypeChecker_Common.implicits in
           FStarC_Compiler_List.fold_right
             (fun imp ->
                fun uu___3 ->
                  match uu___3 with
                  | (more, imps) ->
                      let uu___4 =
                        FStarC_Syntax_Unionfind.find
                          (imp.FStarC_TypeChecker_Common.imp_uvar).FStarC_Syntax_Syntax.ctx_uvar_head in
                      (match uu___4 with
                       | FStar_Pervasives_Native.Some uu___5 ->
                           (more, (imp :: imps))
                       | FStar_Pervasives_Native.None ->
                           let se =
                             find_user_tac_for_uvar env
                               imp.FStarC_TypeChecker_Common.imp_uvar in
                           (match se with
                            | FStar_Pervasives_Native.None ->
                                (more, (imp :: imps))
                            | FStar_Pervasives_Native.Some se1 ->
                                (((imp, se1) :: more), imps)))) uu___2
             ([], []) in
         match uu___1 with
         | (more, imps) ->
             let bucketize is =
               let map = FStarC_Compiler_Util.smap_create (Prims.of_int (17)) in
               FStarC_Compiler_List.iter
                 (fun uu___3 ->
                    match uu___3 with
                    | (i, s) ->
                        let uu___4 = FStarC_Syntax_Util.lid_of_sigelt s in
                        (match uu___4 with
                         | FStar_Pervasives_Native.None ->
                             failwith "Unexpected: tactic without a name"
                         | FStar_Pervasives_Native.Some l ->
                             let lstr = FStarC_Ident.string_of_lid l in
                             let uu___5 =
                               FStarC_Compiler_Util.smap_try_find map lstr in
                             (match uu___5 with
                              | FStar_Pervasives_Native.None ->
                                  FStarC_Compiler_Util.smap_add map lstr
                                    ([i], s)
                              | FStar_Pervasives_Native.Some (is1, s1) ->
                                  (FStarC_Compiler_Util.smap_remove map lstr;
                                   FStarC_Compiler_Util.smap_add map lstr
                                     ((i :: is1), s1))))) is;
               FStarC_Compiler_Util.smap_fold map
                 (fun uu___3 -> fun is1 -> fun out -> is1 :: out) [] in
             let buckets = bucketize (FStarC_Compiler_List.op_At eqs more) in
             (FStarC_Compiler_List.iter
                (fun uu___3 ->
                   match uu___3 with
                   | (imps1, sigel) -> solve_goals_with_tac env g imps1 sigel)
                buckets;
              (let uu___3 =
                 FStarC_Class_Listlike.from_list
                   (FStarC_Compiler_CList.listlike_clist ()) imps in
               {
                 FStarC_TypeChecker_Common.guard_f =
                   (g.FStarC_TypeChecker_Common.guard_f);
                 FStarC_TypeChecker_Common.deferred_to_tac =
                   (Obj.magic
                      (FStarC_Class_Listlike.empty ()
                         (Obj.magic (FStarC_Compiler_CList.listlike_clist ()))));
                 FStarC_TypeChecker_Common.deferred =
                   (g.FStarC_TypeChecker_Common.deferred);
                 FStarC_TypeChecker_Common.univ_ineqs =
                   (g.FStarC_TypeChecker_Common.univ_ineqs);
                 FStarC_TypeChecker_Common.implicits = uu___3
               })))