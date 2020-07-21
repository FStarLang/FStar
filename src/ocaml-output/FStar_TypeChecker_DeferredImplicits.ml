open Prims
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____12 = FStar_Syntax_Util.head_and_args t in
    match uu____12 with
    | (head, _args) ->
        let uu____55 =
          let uu____56 = FStar_Syntax_Subst.compress head in
          uu____56.FStar_Syntax_Syntax.n in
        (match uu____55 with
         | FStar_Syntax_Syntax.Tm_uvar uu____59 -> true
         | uu____72 -> false)
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t ->
    let uu____78 = FStar_Syntax_Util.head_and_args t in
    match uu____78 with
    | (head, _args) ->
        let uu____121 =
          let uu____122 = FStar_Syntax_Subst.compress head in
          uu____122.FStar_Syntax_Syntax.n in
        (match uu____121 with
         | FStar_Syntax_Syntax.Tm_uvar (u, uu____126) -> u
         | uu____143 -> failwith "Not a flex-uvar")
type goal_type =
  | FlexRigid of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | FlexFlex of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar)
  
  | Can_be_split_into of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term
  * FStar_Syntax_Syntax.ctx_uvar) 
  | Imp of FStar_Syntax_Syntax.ctx_uvar 
let (uu___is_FlexRigid : goal_type -> Prims.bool) =
  fun projectee ->
    match projectee with | FlexRigid _0 -> true | uu____188 -> false
let (__proj__FlexRigid__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | FlexRigid _0 -> _0
let (uu___is_FlexFlex : goal_type -> Prims.bool) =
  fun projectee ->
    match projectee with | FlexFlex _0 -> true | uu____217 -> false
let (__proj__FlexFlex__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar))
  = fun projectee -> match projectee with | FlexFlex _0 -> _0
let (uu___is_Can_be_split_into : goal_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Can_be_split_into _0 -> true | uu____248 -> false
let (__proj__Can_be_split_into__item___0 :
  goal_type ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.ctx_uvar))
  = fun projectee -> match projectee with | Can_be_split_into _0 -> _0
let (uu___is_Imp : goal_type -> Prims.bool) =
  fun projectee -> match projectee with | Imp _0 -> true | uu____279 -> false
let (__proj__Imp__item___0 : goal_type -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee -> match projectee with | Imp _0 -> _0
type goal_dep =
  {
  goal_dep_id: Prims.int ;
  goal_type: goal_type ;
  goal_imp: FStar_TypeChecker_Common.implicit ;
  assignees: FStar_Syntax_Syntax.ctx_uvar FStar_Util.set ;
  goal_dep_uvars: FStar_Syntax_Syntax.ctx_uvar FStar_Util.set ;
  dependences: goal_dep Prims.list FStar_ST.ref ;
  visited: Prims.int FStar_ST.ref }
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
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> assignees
let (__proj__Mkgoal_dep__item__goal_dep_uvars :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> goal_dep_uvars
let (__proj__Mkgoal_dep__item__dependences :
  goal_dep -> goal_dep Prims.list FStar_ST.ref) =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> dependences
let (__proj__Mkgoal_dep__item__visited : goal_dep -> Prims.int FStar_ST.ref)
  =
  fun projectee ->
    match projectee with
    | { goal_dep_id; goal_type = goal_type1; goal_imp; assignees;
        goal_dep_uvars; dependences; visited;_} -> visited
type goal_deps = goal_dep Prims.list
let (print_uvar_set :
  FStar_Syntax_Syntax.ctx_uvar FStar_Util.set -> Prims.string) =
  fun s ->
    let uu____520 =
      let uu____523 = FStar_Util.set_elements s in
      FStar_All.pipe_right uu____523
        (FStar_List.map
           (fun u ->
              let uu____533 =
                let uu____534 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_All.pipe_left FStar_Util.string_of_int uu____534 in
              Prims.op_Hat "?" uu____533)) in
    FStar_All.pipe_right uu____520 (FStar_String.concat "; ")
let (print_goal_dep : goal_dep -> Prims.string) =
  fun gd ->
    let uu____542 = FStar_Util.string_of_int gd.goal_dep_id in
    let uu____543 = print_uvar_set gd.assignees in
    let uu____544 =
      let uu____545 =
        let uu____548 = FStar_ST.op_Bang gd.dependences in
        FStar_List.map (fun gd1 -> FStar_Util.string_of_int gd1.goal_dep_id)
          uu____548 in
      FStar_All.pipe_right uu____545 (FStar_String.concat "; ") in
    let uu____565 =
      FStar_Syntax_Print.ctx_uvar_to_string
        (gd.goal_imp).FStar_TypeChecker_Common.imp_uvar in
    FStar_Util.format4 "%s:{assignees=[%s], dependences=[%s]}\n\t%s\n"
      uu____542 uu____543 uu____544 uu____565
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
          FStar_All.pipe_right hooks
            (FStar_Util.try_find
               (fun hook ->
                  FStar_All.pipe_right hook.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some (FStar_Syntax_Util.attr_eq a))))
      | uu____594 -> FStar_Pervasives_Native.None
let (should_defer_uvar_to_user_tac :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun env ->
    fun u ->
      if Prims.op_Negation env.FStar_TypeChecker_Env.enable_defer_to_tac
      then false
      else
        (let uu____608 = find_user_tac_for_uvar env u in
         FStar_Option.isSome uu____608)
let solve_goals_with_tac :
  'uuuuuu621 .
    FStar_TypeChecker_Env.env ->
      'uuuuuu621 ->
        FStar_TypeChecker_Common.implicits ->
          FStar_Syntax_Syntax.sigelt -> unit
  =
  fun env ->
    fun g ->
      fun deferred_goals ->
        fun tac ->
          let resolve_tac =
            match tac.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_let (uu____643, lid::[]) ->
                let qn = FStar_TypeChecker_Env.lookup_qname env lid in
                let fv =
                  FStar_Syntax_Syntax.lid_as_fv lid
                    (FStar_Syntax_Syntax.Delta_constant_at_level
                       Prims.int_zero) FStar_Pervasives_Native.None in
                let dd =
                  let uu____650 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn in
                  match uu____650 with
                  | FStar_Pervasives_Native.Some dd -> dd
                  | FStar_Pervasives_Native.None -> failwith "Expected a dd" in
                let term =
                  let uu____655 =
                    FStar_Syntax_Syntax.lid_as_fv lid dd
                      FStar_Pervasives_Native.None in
                  FStar_Syntax_Syntax.fv_to_tm uu____655 in
                term
            | uu____656 -> failwith "Resolve_tac not found" in
          let env1 =
            let uu___74_658 = env in
            {
              FStar_TypeChecker_Env.solver =
                (uu___74_658.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___74_658.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___74_658.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___74_658.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___74_658.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___74_658.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___74_658.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___74_658.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___74_658.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___74_658.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___74_658.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___74_658.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___74_658.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___74_658.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___74_658.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___74_658.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___74_658.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___74_658.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___74_658.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___74_658.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___74_658.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___74_658.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___74_658.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___74_658.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___74_658.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___74_658.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___74_658.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___74_658.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___74_658.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___74_658.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___74_658.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___74_658.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___74_658.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___74_658.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___74_658.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___74_658.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___74_658.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___74_658.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___74_658.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___74_658.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___74_658.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___74_658.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___74_658.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___74_658.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___74_658.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___74_658.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac = false
            } in
          env1.FStar_TypeChecker_Env.try_solve_implicits_hook env1
            resolve_tac deferred_goals
let (solve_deferred_to_tactic_goals :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let deferred = g.FStar_TypeChecker_Common.deferred_to_tac in
      let prob_as_implicit uu____683 =
        match uu____683 with
        | (reason, prob) ->
            (match prob with
             | FStar_TypeChecker_Common.TProb tp when
                 tp.FStar_TypeChecker_Common.relation =
                   FStar_TypeChecker_Common.EQ
                 ->
                 let uu____701 = FStar_TypeChecker_Env.clear_expected_typ env in
                 (match uu____701 with
                  | (env1, uu____713) ->
                      let env2 =
                        let uu___89_719 = env1 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___89_719.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___89_719.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___89_719.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            ((tp.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___89_719.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___89_719.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___89_719.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___89_719.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___89_719.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___89_719.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___89_719.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___89_719.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___89_719.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___89_719.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___89_719.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___89_719.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___89_719.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___89_719.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___89_719.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___89_719.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___89_719.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___89_719.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___89_719.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___89_719.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___89_719.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___89_719.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___89_719.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___89_719.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___89_719.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___89_719.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___89_719.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___89_719.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___89_719.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___89_719.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___89_719.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___89_719.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___89_719.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___89_719.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___89_719.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___89_719.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___89_719.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___89_719.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___89_719.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___89_719.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___89_719.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___89_719.FStar_TypeChecker_Env.erasable_types_tab);
                          FStar_TypeChecker_Env.enable_defer_to_tac =
                            (uu___89_719.FStar_TypeChecker_Env.enable_defer_to_tac)
                        } in
                      let env_lax =
                        let uu___92_721 = env2 in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___92_721.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___92_721.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___92_721.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___92_721.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___92_721.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___92_721.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___92_721.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___92_721.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___92_721.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___92_721.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___92_721.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___92_721.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___92_721.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___92_721.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___92_721.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___92_721.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___92_721.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (uu___92_721.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___92_721.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___92_721.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax = true;
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___92_721.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___92_721.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___92_721.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___92_721.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___92_721.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___92_721.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___92_721.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___92_721.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___92_721.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts = true;
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___92_721.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___92_721.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___92_721.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___92_721.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___92_721.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___92_721.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___92_721.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (uu___92_721.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___92_721.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___92_721.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___92_721.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___92_721.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___92_721.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___92_721.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___92_721.FStar_TypeChecker_Env.erasable_types_tab);
                          FStar_TypeChecker_Env.enable_defer_to_tac =
                            (uu___92_721.FStar_TypeChecker_Env.enable_defer_to_tac)
                        } in
                      let uu____722 =
                        let uu____729 =
                          is_flex tp.FStar_TypeChecker_Common.lhs in
                        if uu____729
                        then
                          env2.FStar_TypeChecker_Env.type_of env_lax
                            tp.FStar_TypeChecker_Common.lhs
                        else
                          env2.FStar_TypeChecker_Env.type_of env_lax
                            tp.FStar_TypeChecker_Common.rhs in
                      (match uu____722 with
                       | (uu____741, t_eq, uu____743) ->
                           let goal_ty =
                             let uu____745 =
                               env2.FStar_TypeChecker_Env.universe_of env_lax
                                 t_eq in
                             FStar_Syntax_Util.mk_eq2 uu____745 t_eq
                               tp.FStar_TypeChecker_Common.lhs
                               tp.FStar_TypeChecker_Common.rhs in
                           let uu____746 =
                             FStar_TypeChecker_Env.new_implicit_var_aux
                               reason
                               (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                               env2 goal_ty FStar_Syntax_Syntax.Strict
                               FStar_Pervasives_Native.None in
                           (match uu____746 with
                            | (goal, ctx_uvar, uu____765) ->
                                let imp =
                                  let uu____779 =
                                    let uu____780 = FStar_List.hd ctx_uvar in
                                    FStar_Pervasives_Native.fst uu____780 in
                                  {
                                    FStar_TypeChecker_Common.imp_reason = "";
                                    FStar_TypeChecker_Common.imp_uvar =
                                      uu____779;
                                    FStar_TypeChecker_Common.imp_tm = goal;
                                    FStar_TypeChecker_Common.imp_range =
                                      ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                  } in
                                let sigelt =
                                  let uu____792 =
                                    is_flex tp.FStar_TypeChecker_Common.lhs in
                                  if uu____792
                                  then
                                    let uu____795 =
                                      flex_uvar_head
                                        tp.FStar_TypeChecker_Common.lhs in
                                    find_user_tac_for_uvar env2 uu____795
                                  else
                                    (let uu____797 =
                                       is_flex
                                         tp.FStar_TypeChecker_Common.rhs in
                                     if uu____797
                                     then
                                       let uu____800 =
                                         flex_uvar_head
                                           tp.FStar_TypeChecker_Common.rhs in
                                       find_user_tac_for_uvar env2 uu____800
                                     else FStar_Pervasives_Native.None) in
                                (match sigelt with
                                 | FStar_Pervasives_Native.None ->
                                     failwith
                                       "Impossible: No tactic associated with deferred problem"
                                 | FStar_Pervasives_Native.Some se ->
                                     (imp, se)))))
             | uu____811 -> failwith "Unexpected problem deferred to tactic") in
      let eqs =
        FStar_List.map prob_as_implicit
          g.FStar_TypeChecker_Common.deferred_to_tac in
      let uu____831 =
        FStar_List.fold_right
          (fun imp ->
             fun uu____863 ->
               match uu____863 with
               | (more, imps) ->
                   let uu____906 =
                     FStar_Syntax_Unionfind.find
                       (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                   (match uu____906 with
                    | FStar_Pervasives_Native.Some uu____921 ->
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
      match uu____831 with
      | (more, imps) ->
          let bucketize is =
            let map = FStar_Util.smap_create (Prims.of_int (17)) in
            FStar_List.iter
              (fun uu____1046 ->
                 match uu____1046 with
                 | (i, s) ->
                     let uu____1053 = FStar_Syntax_Util.lid_of_sigelt s in
                     (match uu____1053 with
                      | FStar_Pervasives_Native.None ->
                          failwith "Unexpected: tactic without a name"
                      | FStar_Pervasives_Native.Some l ->
                          let lstr = FStar_Ident.string_of_lid l in
                          let uu____1058 = FStar_Util.smap_try_find map lstr in
                          (match uu____1058 with
                           | FStar_Pervasives_Native.None ->
                               FStar_Util.smap_add map lstr ([i], s)
                           | FStar_Pervasives_Native.Some (is1, s1) ->
                               (FStar_Util.smap_remove map lstr;
                                FStar_Util.smap_add map lstr ((i :: is1), s1)))))
              is;
            FStar_Util.smap_fold map
              (fun uu____1105 -> fun is1 -> fun out -> is1 :: out) [] in
          let buckets = bucketize (FStar_List.append eqs more) in
          (FStar_List.iter
             (fun uu____1145 ->
                match uu____1145 with
                | (imps1, sigel) -> solve_goals_with_tac env g imps1 sigel)
             buckets;
           (let uu___153_1152 = g in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___153_1152.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac = [];
              FStar_TypeChecker_Common.deferred =
                (uu___153_1152.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___153_1152.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = imps
            }))