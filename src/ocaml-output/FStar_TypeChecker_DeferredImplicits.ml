open Prims
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args_full t in
    match uu___ with
    | (head, _args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress head in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_uvar uu___2 -> true
         | uu___2 -> false)
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args_full t in
    match uu___ with
    | (head, _args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress head in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_uvar (u, uu___2) -> u
         | uu___2 -> failwith "Not a flex-uvar")
type goal_type =
  | FlexRigid of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | FlexFlex of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar)
  
  | Can_be_split_into of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term
  * FStar_Syntax_Syntax.ctx_uvar) 
  | Imp of FStar_Syntax_Syntax.ctx_uvar 
let (uu___is_FlexRigid : goal_type -> Prims.bool) =
  fun projectee ->
    match projectee with | FlexRigid _0 -> true | uu___ -> false
let (__proj__FlexRigid__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | FlexRigid _0 -> _0
let (uu___is_FlexFlex : goal_type -> Prims.bool) =
  fun projectee ->
    match projectee with | FlexFlex _0 -> true | uu___ -> false
let (__proj__FlexFlex__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar))
  = fun projectee -> match projectee with | FlexFlex _0 -> _0
let (uu___is_Can_be_split_into : goal_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Can_be_split_into _0 -> true | uu___ -> false
let (__proj__Can_be_split_into__item___0 :
  goal_type ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.ctx_uvar))
  = fun projectee -> match projectee with | Can_be_split_into _0 -> _0
let (uu___is_Imp : goal_type -> Prims.bool) =
  fun projectee -> match projectee with | Imp _0 -> true | uu___ -> false
let (__proj__Imp__item___0 : goal_type -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee -> match projectee with | Imp _0 -> _0
type goal_dep =
  {
  goal_dep_id: Prims.int ;
  goal_type: goal_type ;
  goal_imp: FStar_TypeChecker_Common.implicit ;
  assignees: FStar_Syntax_Syntax.ctx_uvar FStar_Compiler_Util.set ;
  goal_dep_uvars: FStar_Syntax_Syntax.ctx_uvar FStar_Compiler_Util.set ;
  dependences: goal_dep Prims.list FStar_Compiler_Effect.ref ;
  visited: Prims.int FStar_Compiler_Effect.ref }
let (__proj__Mkgoal_dep__item__goal_dep_id : goal_dep -> Prims.int) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> goal_dep_id
let (__proj__Mkgoal_dep__item__goal_type : goal_dep -> goal_type) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> goal_type1
let (__proj__Mkgoal_dep__item__goal_imp :
  goal_dep -> FStar_TypeChecker_Common.implicit) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> goal_imp
let (__proj__Mkgoal_dep__item__assignees :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Compiler_Util.set) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> assignees
let (__proj__Mkgoal_dep__item__goal_dep_uvars :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Compiler_Util.set) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> goal_dep_uvars
let (__proj__Mkgoal_dep__item__dependences :
  goal_dep -> goal_dep Prims.list FStar_Compiler_Effect.ref) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> dependences
let (__proj__Mkgoal_dep__item__visited :
  goal_dep -> Prims.int FStar_Compiler_Effect.ref) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> visited
type goal_deps = goal_dep Prims.list
let (print_uvar_set :
  FStar_Syntax_Syntax.ctx_uvar FStar_Compiler_Util.set -> Prims.string) =
  fun s ->
    let uu___ =
      let uu___1 = FStar_Compiler_Util.set_elements s in
      FStar_Compiler_Effect.op_Bar_Greater uu___1
        (FStar_Compiler_List.map
           (fun u ->
              let uu___2 =
                let uu___3 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_Compiler_Effect.op_Less_Bar
                  FStar_Compiler_Util.string_of_int uu___3 in
              Prims.op_Hat "?" uu___2)) in
    FStar_Compiler_Effect.op_Bar_Greater uu___ (FStar_String.concat "; ")
let (print_goal_dep : goal_dep -> Prims.string) =
  fun gd ->
    let uu___ = FStar_Compiler_Util.string_of_int gd.goal_dep_id in
    let uu___1 = print_uvar_set gd.assignees in
    let uu___2 =
      let uu___3 =
        let uu___4 = FStar_Compiler_Effect.op_Bang gd.dependences in
        FStar_Compiler_List.map
          (fun gd1 -> FStar_Compiler_Util.string_of_int gd1.goal_dep_id)
          uu___4 in
      FStar_Compiler_Effect.op_Bar_Greater uu___3 (FStar_String.concat "; ") in
    let uu___3 =
      FStar_Syntax_Print.ctx_uvar_to_string
        (gd.goal_imp).FStar_TypeChecker_Common.imp_uvar in
    FStar_Compiler_Util.format4
      "%s:{assignees=[%s], dependences=[%s]}\n\t%s\n" uu___ uu___1 uu___2
      uu___3
let (find_user_tac_for_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env ->
    fun u ->
      match u.FStar_Syntax_Syntax.ctx_uvar_meta with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
          a) ->
          let hooks =
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string in
          FStar_Compiler_Effect.op_Bar_Greater hooks
            (FStar_Compiler_Util.try_find
               (fun hook ->
                  FStar_Compiler_Effect.op_Bar_Greater
                    hook.FStar_Syntax_Syntax.sigattrs
                    (FStar_Compiler_Util.for_some
                       (FStar_Syntax_Util.attr_eq a))))
      | uu___ -> FStar_Pervasives_Native.None
let (should_defer_uvar_to_user_tac :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun env ->
    fun u ->
      if Prims.op_Negation env.FStar_TypeChecker_Env.enable_defer_to_tac
      then false
      else
        (let uu___1 = find_user_tac_for_uvar env u in
         FStar_Compiler_Option.isSome uu___1)
let solve_goals_with_tac :
  'uuuuu .
    FStar_TypeChecker_Env.env ->
      'uuuuu ->
        FStar_TypeChecker_Common.implicits ->
          FStar_Syntax_Syntax.sigelt -> unit
  =
  fun env ->
    fun g ->
      fun deferred_goals ->
        fun tac ->
          let resolve_tac =
            match tac.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let (uu___, lid::[]) ->
                let qn = FStar_TypeChecker_Env.lookup_qname env lid in
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv lid
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero) FStar_Pervasives_Native.None in
                let dd =
                  let uu___1 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn in
                  match uu___1 with
                  | FStar_Pervasives_Native.Some dd1 -> dd1
                  | FStar_Pervasives_Native.None -> failwith "Expected a dd" in
                let term =
                  let uu___1 =
                    FStar_Syntax_Syntax.lid_as_fv lid dd
                      FStar_Pervasives_Native.None in
                  FStar_Syntax_Syntax.fv_to_tm uu___1 in
                term
            | uu___ -> failwith "Resolve_tac not found" in
          let env1 =
            {
              FStar_TypeChecker_Env.solver =
                (env.FStar_TypeChecker_Env.solver);
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
              FStar_TypeChecker_Env.sigtab =
                (env.FStar_TypeChecker_Env.sigtab);
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
              FStar_TypeChecker_Env.use_eq =
                (env.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (env.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (env.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (env.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (env.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (env.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (env.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (env.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (env.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStar_TypeChecker_Env.universe_of =
                (env.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStar_TypeChecker_Env.use_bv_sorts =
                (env.FStar_TypeChecker_Env.use_bv_sorts);
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
              FStar_TypeChecker_Env.splice =
                (env.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (env.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (env.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (env.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (env.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv = (env.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (env.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (env.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac = false;
              FStar_TypeChecker_Env.unif_allow_ref_guards =
                (env.FStar_TypeChecker_Env.unif_allow_ref_guards)
            } in
          env1.FStar_TypeChecker_Env.try_solve_implicits_hook env1
            resolve_tac deferred_goals
let (solve_deferred_to_tactic_goals :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      if Prims.op_Negation env.FStar_TypeChecker_Env.enable_defer_to_tac
      then g
      else
        (let deferred = g.FStar_TypeChecker_Common.deferred_to_tac in
         let prob_as_implicit uu___1 =
           match uu___1 with
           | (uu___2, reason, prob) ->
               (match prob with
                | FStar_TypeChecker_Common.TProb tp when
                    tp.FStar_TypeChecker_Common.relation =
                      FStar_TypeChecker_Common.EQ
                    ->
                    let uu___3 = FStar_TypeChecker_Env.clear_expected_typ env in
                    (match uu___3 with
                     | (env1, uu___4) ->
                         let env2 =
                           {
                             FStar_TypeChecker_Env.solver =
                               (env1.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (env1.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (env1.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               ((tp.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (env1.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (env1.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (env1.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (env1.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (env1.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (env1.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (env1.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (env1.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (env1.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (env1.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (env1.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (env1.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (env1.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (env1.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (env1.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (env1.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (env1.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (env1.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (env1.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (env1.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (env1.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (env1.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (env1.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                               (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                             FStar_TypeChecker_Env.universe_of =
                               (env1.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                               =
                               (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (env1.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (env1.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (env1.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (env1.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (env1.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (env1.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (env1.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (env1.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (env1.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (env1.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (env1.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (env1.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (env1.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (env1.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                             FStar_TypeChecker_Env.unif_allow_ref_guards =
                               (env1.FStar_TypeChecker_Env.unif_allow_ref_guards)
                           } in
                         let env_lax =
                           {
                             FStar_TypeChecker_Env.solver =
                               (env2.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (env2.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (env2.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (env2.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (env2.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (env2.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (env2.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (env2.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (env2.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (env2.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (env2.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (env2.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (env2.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (env2.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (env2.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (env2.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (env2.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (env2.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (env2.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (env2.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (env2.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (env2.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (env2.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (env2.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (env2.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (env2.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                               (env2.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                             FStar_TypeChecker_Env.universe_of =
                               (env2.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                               =
                               (env2.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                             FStar_TypeChecker_Env.use_bv_sorts = true;
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (env2.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (env2.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (env2.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (env2.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (env2.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (env2.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (env2.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (env2.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (env2.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (env2.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (env2.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (env2.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (env2.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (env2.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (env2.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               false;
                             FStar_TypeChecker_Env.unif_allow_ref_guards =
                               (env2.FStar_TypeChecker_Env.unif_allow_ref_guards)
                           } in
                         let uu___5 =
                           let t =
                             let uu___6 =
                               is_flex tp.FStar_TypeChecker_Common.lhs in
                             if uu___6
                             then tp.FStar_TypeChecker_Common.lhs
                             else tp.FStar_TypeChecker_Common.rhs in
                           env2.FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                             env_lax t true in
                         (match uu___5 with
                          | (uu___6, t_eq, uu___7) ->
                              let goal_ty =
                                let uu___8 =
                                  env2.FStar_TypeChecker_Env.universe_of
                                    env_lax t_eq in
                                FStar_Syntax_Util.mk_eq2 uu___8 t_eq
                                  tp.FStar_TypeChecker_Common.lhs
                                  tp.FStar_TypeChecker_Common.rhs in
                              let uu___8 =
                                FStar_TypeChecker_Env.new_implicit_var_aux
                                  reason
                                  (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                                  env2 goal_ty
                                  FStar_Syntax_Syntax.Allow_untyped
                                  FStar_Pervasives_Native.None in
                              (match uu___8 with
                               | (goal, ctx_uvar, uu___9) ->
                                   let imp =
                                     let uu___10 =
                                       let uu___11 =
                                         FStar_Compiler_List.hd ctx_uvar in
                                       FStar_Pervasives_Native.fst uu___11 in
                                     {
                                       FStar_TypeChecker_Common.imp_reason =
                                         "";
                                       FStar_TypeChecker_Common.imp_uvar =
                                         uu___10;
                                       FStar_TypeChecker_Common.imp_tm = goal;
                                       FStar_TypeChecker_Common.imp_range =
                                         ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                     } in
                                   let sigelt =
                                     let uu___10 =
                                       is_flex
                                         tp.FStar_TypeChecker_Common.lhs in
                                     if uu___10
                                     then
                                       let uu___11 =
                                         let uu___12 =
                                           flex_uvar_head
                                             tp.FStar_TypeChecker_Common.lhs in
                                         find_user_tac_for_uvar env2 uu___12 in
                                       match uu___11 with
                                       | FStar_Pervasives_Native.None ->
                                           let uu___12 =
                                             is_flex
                                               tp.FStar_TypeChecker_Common.rhs in
                                           (if uu___12
                                            then
                                              let uu___13 =
                                                flex_uvar_head
                                                  tp.FStar_TypeChecker_Common.rhs in
                                              find_user_tac_for_uvar env2
                                                uu___13
                                            else FStar_Pervasives_Native.None)
                                       | v -> v
                                     else
                                       (let uu___12 =
                                          is_flex
                                            tp.FStar_TypeChecker_Common.rhs in
                                        if uu___12
                                        then
                                          let uu___13 =
                                            flex_uvar_head
                                              tp.FStar_TypeChecker_Common.rhs in
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
           FStar_Compiler_List.map prob_as_implicit
             g.FStar_TypeChecker_Common.deferred_to_tac in
         let uu___1 =
           FStar_Compiler_List.fold_right
             (fun imp ->
                fun uu___2 ->
                  match uu___2 with
                  | (more, imps) ->
                      let uu___3 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      (match uu___3 with
                       | FStar_Pervasives_Native.Some uu___4 ->
                           (more, (imp :: imps))
                       | FStar_Pervasives_Native.None ->
                           let se =
                             find_user_tac_for_uvar env
                               imp.FStar_TypeChecker_Common.imp_uvar in
                           (match se with
                            | FStar_Pervasives_Native.None ->
                                (more, (imp :: imps))
                            | FStar_Pervasives_Native.Some se1 ->
                                (((imp, se1) :: more), imps))))
             g.FStar_TypeChecker_Common.implicits ([], []) in
         match uu___1 with
         | (more, imps) ->
             let bucketize is =
               let map = FStar_Compiler_Util.smap_create (Prims.of_int (17)) in
               FStar_Compiler_List.iter
                 (fun uu___3 ->
                    match uu___3 with
                    | (i, s) ->
                        let uu___4 = FStar_Syntax_Util.lid_of_sigelt s in
                        (match uu___4 with
                         | FStar_Pervasives_Native.None ->
                             failwith "Unexpected: tactic without a name"
                         | FStar_Pervasives_Native.Some l ->
                             let lstr = FStar_Ident.string_of_lid l in
                             let uu___5 =
                               FStar_Compiler_Util.smap_try_find map lstr in
                             (match uu___5 with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Compiler_Util.smap_add map lstr
                                    ([i], s)
                              | FStar_Pervasives_Native.Some (is1, s1) ->
                                  (FStar_Compiler_Util.smap_remove map lstr;
                                   FStar_Compiler_Util.smap_add map lstr
                                     ((i :: is1), s1))))) is;
               FStar_Compiler_Util.smap_fold map
                 (fun uu___3 -> fun is1 -> fun out -> is1 :: out) [] in
             let buckets = bucketize (FStar_Compiler_List.op_At eqs more) in
             (FStar_Compiler_List.iter
                (fun uu___3 ->
                   match uu___3 with
                   | (imps1, sigel) -> solve_goals_with_tac env g imps1 sigel)
                buckets;
              {
                FStar_TypeChecker_Common.guard_f =
                  (g.FStar_TypeChecker_Common.guard_f);
                FStar_TypeChecker_Common.deferred_to_tac = [];
                FStar_TypeChecker_Common.deferred =
                  (g.FStar_TypeChecker_Common.deferred);
                FStar_TypeChecker_Common.univ_ineqs =
                  (g.FStar_TypeChecker_Common.univ_ineqs);
                FStar_TypeChecker_Common.implicits = imps
              }))