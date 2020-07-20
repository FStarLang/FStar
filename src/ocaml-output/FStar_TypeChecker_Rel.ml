open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar
type lstring = Prims.string FStar_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStar_Thunk.thunk) =
  fun f ->
    let uf = FStar_Syntax_Unionfind.get () in
    FStar_Thunk.mk
      (fun uu____36 ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         FStar_Syntax_Unionfind.set uf;
         (let r = f () in FStar_Syntax_Unionfind.rollback tx; r))
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee -> match projectee with | TERM _0 -> true | uu____69 -> false
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | TERM _0 -> _0
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee -> match projectee with | UNIV _0 -> true | uu____98 -> false
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee -> match projectee with | UNIV _0 -> _0
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ;
  wl_deferred_to_tac:
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Common.implicits ;
  repr_subcomp_allowed: Prims.bool }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        attempting
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        wl_deferred
let (__proj__Mkworklist__item__wl_deferred_to_tac :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        wl_deferred_to_tac
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        ctr
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        defer_ok
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        smt_ok
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        umax_heuristic_ok
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        tcenv
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        wl_implicits
let (__proj__Mkworklist__item__repr_subcomp_allowed : worklist -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        repr_subcomp_allowed
let (as_deferred :
  (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ->
    FStar_TypeChecker_Common.deferred)
  =
  fun wl_def ->
    FStar_List.map
      (fun uu____573 ->
         match uu____573 with
         | (uu____586, m, p) ->
             let uu____593 = FStar_Thunk.force m in (uu____593, p)) wl_def
let (as_wl_deferred :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun wl ->
    fun d ->
      FStar_List.map
        (fun uu____636 ->
           match uu____636 with
           | (m, p) ->
               let uu____651 = FStar_Thunk.mkv m in ((wl.ctr), uu____651, p))
        d
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              FStar_Syntax_Syntax.should_check_uvar ->
                FStar_Syntax_Syntax.ctx_uvar_meta_t
                  FStar_Pervasives_Native.option ->
                  (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
                    worklist))
  =
  fun reason ->
    fun wl ->
      fun r ->
        fun gamma ->
          fun binders ->
            fun k ->
              fun should_check ->
                fun meta ->
                  let ctx_uvar =
                    let uu____737 = FStar_Syntax_Unionfind.fresh r in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____737;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                      FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                      FStar_Syntax_Syntax.ctx_uvar_typ = k;
                      FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                      FStar_Syntax_Syntax.ctx_uvar_should_check =
                        should_check;
                      FStar_Syntax_Syntax.ctx_uvar_range = r;
                      FStar_Syntax_Syntax.ctx_uvar_meta = meta
                    } in
                  FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                    true gamma binders;
                  (let t =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_uvar
                          (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange))) r in
                   let imp =
                     {
                       FStar_TypeChecker_Common.imp_reason = reason;
                       FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Common.imp_tm = t;
                       FStar_TypeChecker_Common.imp_range = r
                     } in
                   (let uu____770 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace") in
                    if uu____770
                    then
                      let uu____771 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____771
                    else ());
                   (ctx_uvar, t,
                     ((let uu___94_774 = wl in
                       {
                         attempting = (uu___94_774.attempting);
                         wl_deferred = (uu___94_774.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___94_774.wl_deferred_to_tac);
                         ctr = (uu___94_774.ctr);
                         defer_ok = (uu___94_774.defer_ok);
                         smt_ok = (uu___94_774.smt_ok);
                         umax_heuristic_ok = (uu___94_774.umax_heuristic_ok);
                         tcenv = (uu___94_774.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits));
                         repr_subcomp_allowed =
                           (uu___94_774.repr_subcomp_allowed)
                       }))))
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        worklist ->
          (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
            worklist))
  =
  fun u ->
    fun bs ->
      fun t ->
        fun wl ->
          let env =
            let uu___100_806 = wl.tcenv in
            {
              FStar_TypeChecker_Env.solver =
                (uu___100_806.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___100_806.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___100_806.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___100_806.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___100_806.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___100_806.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___100_806.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___100_806.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___100_806.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___100_806.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___100_806.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___100_806.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___100_806.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___100_806.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___100_806.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___100_806.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___100_806.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___100_806.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___100_806.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___100_806.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___100_806.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___100_806.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___100_806.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___100_806.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___100_806.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___100_806.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___100_806.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___100_806.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___100_806.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___100_806.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___100_806.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___100_806.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___100_806.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___100_806.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___100_806.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___100_806.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___100_806.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___100_806.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___100_806.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___100_806.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___100_806.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___100_806.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___100_806.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___100_806.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___100_806.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___100_806.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let env1 = FStar_TypeChecker_Env.push_binders env bs in
          let uu____808 = FStar_TypeChecker_Env.all_binders env1 in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____808 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee ->
    match projectee with | Success _0 -> true | uu____854 -> false
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred *
      FStar_TypeChecker_Common.implicits))
  = fun projectee -> match projectee with | Success _0 -> _0
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee ->
    match projectee with | Failed _0 -> true | uu____889 -> false
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee -> match projectee with | Failed _0 -> _0
let (extend_wl :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      FStar_TypeChecker_Common.implicits -> worklist)
  =
  fun wl ->
    fun defer_to_tac ->
      fun imps ->
        let uu___109_923 = wl in
        let uu____924 =
          let uu____933 = as_wl_deferred wl defer_to_tac in
          FStar_List.append wl.wl_deferred_to_tac uu____933 in
        {
          attempting = (uu___109_923.attempting);
          wl_deferred = (uu___109_923.wl_deferred);
          wl_deferred_to_tac = uu____924;
          ctr = (uu___109_923.ctr);
          defer_ok = (uu___109_923.defer_ok);
          smt_ok = (uu___109_923.smt_ok);
          umax_heuristic_ok = (uu___109_923.umax_heuristic_ok);
          tcenv = (uu___109_923.tcenv);
          wl_implicits = (FStar_List.append wl.wl_implicits imps);
          repr_subcomp_allowed = (uu___109_923.repr_subcomp_allowed)
        }
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | COVARIANT -> true | uu____953 -> false
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | CONTRAVARIANT -> true | uu____959 -> false
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | INVARIANT -> true | uu____965 -> false
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_980 ->
    match uu___0_980 with
    | FStar_TypeChecker_Common.EQ -> "="
    | FStar_TypeChecker_Common.SUB -> "<:"
    | FStar_TypeChecker_Common.SUBINV -> ":>"
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let uu____986 = FStar_Syntax_Util.head_and_args t in
    match uu____986 with
    | (head, args) ->
        (match head.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
             let uu____1047 = FStar_Syntax_Print.ctx_uvar_to_string u in
             let uu____1048 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1060 =
                     let uu____1061 = FStar_List.hd s1 in
                     FStar_Syntax_Print.subst_to_string uu____1061 in
                   FStar_Util.format1 "@<%s>" uu____1060 in
             let uu____1064 = FStar_Syntax_Print.args_to_string args in
             FStar_Util.format3 "%s%s %s" uu____1047 uu____1048 uu____1064
         | uu____1065 -> FStar_Syntax_Print.term_to_string t)
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env ->
    fun uu___1_1075 ->
      match uu___1_1075 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1079 =
            let uu____1082 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____1083 =
              let uu____1086 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____1087 =
                let uu____1090 =
                  let uu____1093 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____1093] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1090 in
              uu____1086 :: uu____1087 in
            uu____1082 :: uu____1083 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1079
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1097 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1098 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____1099 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1097 uu____1098
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1099
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env ->
    fun uu___2_1109 ->
      match uu___2_1109 with
      | UNIV (u, t) ->
          let x =
            let uu____1113 = FStar_Options.hide_uvar_nums () in
            if uu____1113
            then "?"
            else
              (let uu____1115 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____1115 FStar_Util.string_of_int) in
          let uu____1116 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s <- %s" x uu____1116
      | TERM (u, t) ->
          let x =
            let uu____1120 = FStar_Options.hide_uvar_nums () in
            if uu____1120
            then "?"
            else
              (let uu____1122 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               FStar_All.pipe_right uu____1122 FStar_Util.string_of_int) in
          let uu____1123 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s <- %s" x uu____1123
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env -> fun uvis -> FStar_Common.string_of_list (uvi_to_string env) uvis
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms ->
    let uu____1147 =
      let uu____1150 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1150
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1147 (FStar_String.concat ", ")
let args_to_string :
  'uuuuuu1163 .
    (FStar_Syntax_Syntax.term * 'uuuuuu1163) Prims.list -> Prims.string
  =
  fun args ->
    let uu____1181 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1199 ->
              match uu____1199 with
              | (x, uu____1205) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1181 (FStar_String.concat " ")
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env ->
    {
      attempting = [];
      wl_deferred = [];
      wl_deferred_to_tac = [];
      ctr = Prims.int_zero;
      defer_ok = true;
      smt_ok = true;
      umax_heuristic_ok = true;
      tcenv = env;
      wl_implicits = [];
      repr_subcomp_allowed = false
    }
let (giveup :
  FStar_TypeChecker_Env.env ->
    lstring -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env ->
    fun reason ->
      fun prob ->
        (let uu____1241 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1241
         then
           let uu____1242 = FStar_Thunk.force reason in
           let uu____1243 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1242 uu____1243
         else ());
        Failed (prob, reason)
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env ->
    fun reason ->
      fun prob ->
        let uu____1260 = mklstr (fun uu____1263 -> reason) in
        giveup env uu____1260 prob
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1268 ->
    match uu___3_1268 with
    | FStar_TypeChecker_Common.EQ -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV -> FStar_TypeChecker_Common.SUB
let invert :
  'uuuuuu1273 .
    'uuuuuu1273 FStar_TypeChecker_Common.problem ->
      'uuuuuu1273 FStar_TypeChecker_Common.problem
  =
  fun p ->
    let uu___169_1285 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___169_1285.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___169_1285.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___169_1285.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___169_1285.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___169_1285.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___169_1285.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___169_1285.FStar_TypeChecker_Common.rank)
    }
let maybe_invert :
  'uuuuuu1292 .
    'uuuuuu1292 FStar_TypeChecker_Common.problem ->
      'uuuuuu1292 FStar_TypeChecker_Common.problem
  =
  fun p ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1309 ->
    match uu___4_1309 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1315 -> FStar_TypeChecker_Common.TProb uu____1315)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1321 -> FStar_TypeChecker_Common.CProb uu____1321)
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1326 ->
    match uu___5_1326 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___181_1332 = p in
           {
             FStar_TypeChecker_Common.pid =
               (uu___181_1332.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___181_1332.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___181_1332.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___181_1332.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___181_1332.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___181_1332.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___181_1332.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___181_1332.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___181_1332.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___185_1340 = p in
           {
             FStar_TypeChecker_Common.pid =
               (uu___185_1340.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___185_1340.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___185_1340.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___185_1340.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___185_1340.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___185_1340.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___185_1340.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___185_1340.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___185_1340.FStar_TypeChecker_Common.rank)
           })
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel ->
    fun uu___6_1352 ->
      match uu___6_1352 with
      | INVARIANT -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT -> invert_rel rel
      | COVARIANT -> rel
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1357 ->
    match uu___7_1357 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1368 ->
    match uu___8_1368 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1381 ->
    match uu___9_1381 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1394 ->
    match uu___10_1394 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1407 ->
    match uu___11_1407 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1420 ->
    match uu___12_1420 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1431 ->
    match uu___13_1431 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
let def_scope_wf :
  'uuuuuu1446 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu1446) Prims.list -> unit
  =
  fun msg ->
    fun rng ->
      fun r ->
        let uu____1474 =
          let uu____1475 = FStar_Options.defensive () in
          Prims.op_Negation uu____1475 in
        if uu____1474
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv, uu____1509)::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs) in
           aux [] r)
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun prob ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1555 =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1579 = FStar_Syntax_Syntax.mk_binder x in
                [uu____1579] in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1555
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1607 =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1631 = FStar_Syntax_Syntax.mk_binder x in
                [uu____1631] in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1607 in
    def_scope_wf "p_scope" (p_loc prob) r; r
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg ->
    fun prob ->
      fun phi ->
        let uu____1674 =
          let uu____1675 = FStar_Options.defensive () in
          Prims.op_Negation uu____1675 in
        if uu____1674
        then ()
        else
          (let uu____1677 =
             let uu____1680 = p_scope prob in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1680 in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1677 phi)
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg ->
    fun prob ->
      fun comp ->
        let uu____1726 =
          let uu____1727 = FStar_Options.defensive () in
          Prims.op_Negation uu____1727 in
        if uu____1726
        then ()
        else
          (let uu____1729 = FStar_Syntax_Util.arrow [] comp in
           def_check_scoped msg prob uu____1729)
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg ->
    fun prob ->
      let uu____1746 =
        let uu____1747 = FStar_Options.defensive () in
        Prims.op_Negation uu____1747 in
      if uu____1746
      then ()
      else
        (let msgf m =
           let uu____1755 =
             let uu____1756 =
               let uu____1757 = FStar_Util.string_of_int (p_pid prob) in
               Prims.op_Hat uu____1757 (Prims.op_Hat "." m) in
             Prims.op_Hat "." uu____1756 in
           Prims.op_Hat msg uu____1755 in
         (let uu____1759 = msgf "scope" in
          let uu____1760 = p_scope prob in
          def_scope_wf uu____1759 (p_loc prob) uu____1760);
         (let uu____1772 = msgf "guard" in
          def_check_scoped uu____1772 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1777 = msgf "lhs" in
                def_check_scoped uu____1777 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1778 = msgf "rhs" in
                def_check_scoped uu____1778 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1783 = msgf "lhs" in
                def_check_scoped_comp uu____1783 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1784 = msgf "rhs" in
                def_check_scoped_comp uu____1784 prob
                  p.FStar_TypeChecker_Common.rhs))))
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl ->
    fun prob ->
      fun smt_ok ->
        let uu___278_1800 = wl in
        {
          attempting = [prob];
          wl_deferred = (uu___278_1800.wl_deferred);
          wl_deferred_to_tac = (uu___278_1800.wl_deferred_to_tac);
          ctr = (uu___278_1800.ctr);
          defer_ok = (uu___278_1800.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___278_1800.umax_heuristic_ok);
          tcenv = (uu___278_1800.tcenv);
          wl_implicits = (uu___278_1800.wl_implicits);
          repr_subcomp_allowed = (uu___278_1800.repr_subcomp_allowed)
        }
let wl_of_guard :
  'uuuuuu1807 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu1807 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env ->
    fun g ->
      let uu___282_1830 = empty_worklist env in
      let uu____1831 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____1831;
        wl_deferred = (uu___282_1830.wl_deferred);
        wl_deferred_to_tac = (uu___282_1830.wl_deferred_to_tac);
        ctr = (uu___282_1830.ctr);
        defer_ok = (uu___282_1830.defer_ok);
        smt_ok = (uu___282_1830.smt_ok);
        umax_heuristic_ok = (uu___282_1830.umax_heuristic_ok);
        tcenv = (uu___282_1830.tcenv);
        wl_implicits = (uu___282_1830.wl_implicits);
        repr_subcomp_allowed = (uu___282_1830.repr_subcomp_allowed)
      }
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason ->
    fun prob ->
      fun wl ->
        let uu___287_1851 = wl in
        {
          attempting = (uu___287_1851.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          wl_deferred_to_tac = (uu___287_1851.wl_deferred_to_tac);
          ctr = (uu___287_1851.ctr);
          defer_ok = (uu___287_1851.defer_ok);
          smt_ok = (uu___287_1851.smt_ok);
          umax_heuristic_ok = (uu___287_1851.umax_heuristic_ok);
          tcenv = (uu___287_1851.tcenv);
          wl_implicits = (uu___287_1851.wl_implicits);
          repr_subcomp_allowed = (uu___287_1851.repr_subcomp_allowed)
        }
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason ->
    fun prob ->
      fun wl ->
        let uu____1873 = FStar_Thunk.mkv reason in defer uu____1873 prob wl
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs ->
    fun wl ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___295_1889 = wl in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___295_1889.wl_deferred);
         wl_deferred_to_tac = (uu___295_1889.wl_deferred_to_tac);
         ctr = (uu___295_1889.ctr);
         defer_ok = (uu___295_1889.defer_ok);
         smt_ok = (uu___295_1889.smt_ok);
         umax_heuristic_ok = (uu___295_1889.umax_heuristic_ok);
         tcenv = (uu___295_1889.tcenv);
         wl_implicits = (uu___295_1889.wl_implicits);
         repr_subcomp_allowed = (uu___295_1889.repr_subcomp_allowed)
       })
let mk_eq2 :
  'uuuuuu1902 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu1902 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl ->
    fun env ->
      fun prob ->
        fun t1 ->
          fun t2 ->
            let uu____1936 = FStar_Syntax_Util.type_u () in
            match uu____1936 with
            | (t_type, u) ->
                let binders = FStar_TypeChecker_Env.all_binders env in
                let uu____1948 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None in
                (match uu____1948 with
                 | (uu____1959, tt, wl1) ->
                     let uu____1962 = FStar_Syntax_Util.mk_eq2 u tt t1 t2 in
                     (uu____1962, wl1))
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_1967 ->
    match uu___14_1967 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____1973 -> FStar_TypeChecker_Common.TProb uu____1973)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____1979 -> FStar_TypeChecker_Common.CProb uu____1979)
          (invert p)
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p ->
    let uu____1985 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____1985 = Prims.int_one
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero in
  fun uu____1995 -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem :
  'uuuuuu2021 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuuu2021 ->
            FStar_TypeChecker_Common.rel ->
              'uuuuuu2021 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuuu2021 FStar_TypeChecker_Common.problem * worklist)
  =
  fun wl ->
    fun scope ->
      fun orig ->
        fun lhs ->
          fun rel ->
            fun rhs ->
              fun elt ->
                fun reason ->
                  let scope1 =
                    match elt with
                    | FStar_Pervasives_Native.None -> scope
                    | FStar_Pervasives_Native.Some x ->
                        let uu____2106 =
                          let uu____2115 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____2115] in
                        FStar_List.append scope uu____2106 in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1 in
                  let gamma =
                    let uu____2158 =
                      let uu____2161 =
                        FStar_List.map
                          (fun b ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1 in
                      FStar_List.rev uu____2161 in
                    FStar_List.append uu____2158
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma in
                  let uu____2180 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None in
                  match uu____2180 with
                  | (ctx_uvar, lg, wl1) ->
                      let prob =
                        let uu____2199 = next_pid () in
                        {
                          FStar_TypeChecker_Common.pid = uu____2199;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        } in
                      (prob, wl1)
let (mk_t_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl ->
    fun scope ->
      fun orig ->
        fun lhs ->
          fun rel ->
            fun rhs ->
              fun elt ->
                fun reason ->
                  def_check_prob (Prims.op_Hat reason ".mk_t.arg") orig;
                  (let uu____2267 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu____2267 with
                   | (p, wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_t")
                          (FStar_TypeChecker_Common.TProb p);
                        ((FStar_TypeChecker_Common.TProb p), wl1)))
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                Prims.string -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl ->
    fun scope ->
      fun orig ->
        fun lhs ->
          fun rel ->
            fun rhs ->
              fun elt ->
                fun reason ->
                  def_check_prob (Prims.op_Hat reason ".mk_c.arg") orig;
                  (let uu____2350 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu____2350 with
                   | (p, wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
let new_problem :
  'uuuuuu2386 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2386 ->
          FStar_TypeChecker_Common.rel ->
            'uuuuuu2386 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('uuuuuu2386 FStar_TypeChecker_Common.problem * worklist)
  =
  fun wl ->
    fun env ->
      fun lhs ->
        fun rel ->
          fun rhs ->
            fun subject ->
              fun loc ->
                fun reason ->
                  let lg_ty =
                    match subject with
                    | FStar_Pervasives_Native.None ->
                        FStar_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2452 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____2452] in
                        let uu____2471 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        FStar_Syntax_Util.arrow bs uu____2471 in
                  let uu____2474 =
                    let uu____2481 = FStar_TypeChecker_Env.all_binders env in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___378_2491 = wl in
                       {
                         attempting = (uu___378_2491.attempting);
                         wl_deferred = (uu___378_2491.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___378_2491.wl_deferred_to_tac);
                         ctr = (uu___378_2491.ctr);
                         defer_ok = (uu___378_2491.defer_ok);
                         smt_ok = (uu___378_2491.smt_ok);
                         umax_heuristic_ok =
                           (uu___378_2491.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___378_2491.wl_implicits);
                         repr_subcomp_allowed =
                           (uu___378_2491.repr_subcomp_allowed)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2481
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None in
                  match uu____2474 with
                  | (ctx_uvar, lg, wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2503 =
                              let uu____2504 =
                                let uu____2513 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.as_arg uu____2513 in
                              [uu____2504] in
                            FStar_Syntax_Syntax.mk_Tm_app lg uu____2503 loc in
                      let prob =
                        let uu____2541 = next_pid () in
                        {
                          FStar_TypeChecker_Common.pid = uu____2541;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = subject;
                          FStar_TypeChecker_Common.logical_guard = lg1;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            ctx_uvar;
                          FStar_TypeChecker_Common.reason = [reason];
                          FStar_TypeChecker_Common.loc = loc;
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        } in
                      (prob, wl1)
let (problem_using_guard :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
            Prims.string ->
              FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem)
  =
  fun orig ->
    fun lhs ->
      fun rel ->
        fun rhs ->
          fun elt ->
            fun reason ->
              let p =
                let uu____2583 = next_pid () in
                {
                  FStar_TypeChecker_Common.pid = uu____2583;
                  FStar_TypeChecker_Common.lhs = lhs;
                  FStar_TypeChecker_Common.relation = rel;
                  FStar_TypeChecker_Common.rhs = rhs;
                  FStar_TypeChecker_Common.element = elt;
                  FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                  FStar_TypeChecker_Common.logical_guard_uvar =
                    (p_guard_uvar orig);
                  FStar_TypeChecker_Common.reason = (reason ::
                    (p_reason orig));
                  FStar_TypeChecker_Common.loc = (p_loc orig);
                  FStar_TypeChecker_Common.rank =
                    FStar_Pervasives_Native.None
                } in
              def_check_prob reason (FStar_TypeChecker_Common.TProb p); p
let guard_on_element :
  'uuuuuu2595 .
    worklist ->
      'uuuuuu2595 FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun wl ->
    fun problem ->
      fun x ->
        fun phi ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              let uu____2628 =
                let uu____2631 =
                  let uu____2632 =
                    let uu____2639 = FStar_Syntax_Syntax.bv_to_name e in
                    (x, uu____2639) in
                  FStar_Syntax_Syntax.NT uu____2632 in
                [uu____2631] in
              FStar_Syntax_Subst.subst uu____2628 phi
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env ->
    fun d ->
      fun s ->
        let uu____2659 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")) in
        if uu____2659
        then
          let uu____2660 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____2661 = prob_to_string env d in
          let uu____2662 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          let uu____2665 = FStar_Thunk.force s in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2660 uu____2661 uu____2662 uu____2665
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ -> "equal to"
             | FStar_TypeChecker_Common.SUB -> "a subtype of"
             | uu____2669 -> failwith "impossible" in
           let uu____2670 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.term_to_string env)
                   tp.FStar_TypeChecker_Common.lhs
                   tp.FStar_TypeChecker_Common.rhs
             | FStar_TypeChecker_Common.CProb cp ->
                 FStar_TypeChecker_Err.print_discrepancy
                   (FStar_TypeChecker_Normalize.comp_to_string env)
                   cp.FStar_TypeChecker_Common.lhs
                   cp.FStar_TypeChecker_Common.rhs in
           match uu____2670 with
           | (lhs, rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let (commit : uvi Prims.list -> unit) =
  fun uvis ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2702 ->
            match uu___15_2702 with
            | UNIV (u, t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2716 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u, t) ->
                ((let uu____2720 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2720 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___16_2749 ->
           match uu___16_2749 with
           | UNIV uu____2752 -> FStar_Pervasives_Native.None
           | TERM (u, t) ->
               let uu____2759 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               if uu____2759
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___17_2783 ->
           match uu___17_2783 with
           | UNIV (u', t) ->
               let uu____2788 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____2788
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2792 -> FStar_Pervasives_Native.None)
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____2803 =
        let uu____2804 =
          let uu____2805 = FStar_Syntax_Util.unmeta t in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2805 in
        FStar_Syntax_Subst.compress uu____2804 in
      FStar_All.pipe_right uu____2803 FStar_Syntax_Util.unlazy_emb
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____2816 =
        let uu____2817 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t in
        FStar_Syntax_Subst.compress uu____2817 in
      FStar_All.pipe_right uu____2816 FStar_Syntax_Util.unlazy_emb
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____2828 =
        let uu____2831 =
          let uu____2832 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.string_of_lid uu____2832 in
        FStar_Pervasives_Native.Some uu____2831 in
      FStar_Profiling.profile (fun uu____2834 -> sn' env t) uu____2828
        "FStar.TypeChecker.Rel.sn"
let (norm_with_steps :
  Prims.string ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun profiling_tag ->
    fun steps ->
      fun env ->
        fun t ->
          let uu____2855 =
            let uu____2858 =
              let uu____2859 = FStar_TypeChecker_Env.current_module env in
              FStar_Ident.string_of_lid uu____2859 in
            FStar_Pervasives_Native.Some uu____2858 in
          FStar_Profiling.profile
            (fun uu____2861 ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____2855
            profiling_tag
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____2867 = FStar_Syntax_Util.head_and_args t in
    match uu____2867 with
    | (h, uu____2885) ->
        let uu____2910 =
          let uu____2911 = FStar_Syntax_Subst.compress h in
          uu____2911.FStar_Syntax_Syntax.n in
        (match uu____2910 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> true
         | uu____2914 -> false)
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____2925 =
        let uu____2928 =
          let uu____2929 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.string_of_lid uu____2929 in
        FStar_Pervasives_Native.Some uu____2928 in
      FStar_Profiling.profile
        (fun uu____2933 ->
           let uu____2934 = should_strongly_reduce t in
           if uu____2934
           then
             let uu____2935 =
               let uu____2936 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t in
               FStar_Syntax_Subst.compress uu____2936 in
             FStar_All.pipe_right uu____2935 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____2925 "FStar.TypeChecker.Rel.whnf"
let norm_arg :
  'uuuuuu2944 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu2944) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu2944)
  =
  fun env ->
    fun t ->
      let uu____2967 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____2967, (FStar_Pervasives_Native.snd t))
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env ->
    fun binders ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____3018 ->
              match uu____3018 with
              | (x, imp) ->
                  let uu____3037 =
                    let uu___484_3038 = x in
                    let uu____3039 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___484_3038.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___484_3038.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3039
                    } in
                  (uu____3037, imp)))
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3062 = aux u3 in FStar_Syntax_Syntax.U_succ uu____3062
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3066 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____3066
        | uu____3069 -> u2 in
      let uu____3070 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3070
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun t0 ->
        let uu____3086 =
          let uu____3089 =
            let uu____3090 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____3090 in
          FStar_Pervasives_Native.Some uu____3089 in
        FStar_Profiling.profile
          (fun uu____3092 ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3086 "FStar.TypeChecker.Rel.normalize_refinement"
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  =
  fun should_delta ->
    fun env ->
      fun t1 ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Env.Weak;
              FStar_TypeChecker_Env.HNF;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else [FStar_TypeChecker_Env.Weak; FStar_TypeChecker_Env.HNF] in
          normalize_refinement steps env1 t in
        let rec aux norm t11 =
          let t12 = FStar_Syntax_Util.unmeta t11 in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
              if norm
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3204 = norm_refinement env t12 in
                 match uu____3204 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1, phi1);
                     FStar_Syntax_Syntax.pos = uu____3219;
                     FStar_Syntax_Syntax.vars = uu____3220;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3244 =
                       let uu____3245 = FStar_Syntax_Print.term_to_string tt in
                       let uu____3246 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3245 uu____3246 in
                     failwith uu____3244)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3260 = FStar_Syntax_Util.unfold_lazy i in
              aux norm uu____3260
          | FStar_Syntax_Syntax.Tm_uinst uu____3261 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3296 =
                   let uu____3297 = FStar_Syntax_Subst.compress t1' in
                   uu____3297.FStar_Syntax_Syntax.n in
                 match uu____3296 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3312 -> aux true t1'
                 | uu____3319 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3334 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3363 =
                   let uu____3364 = FStar_Syntax_Subst.compress t1' in
                   uu____3364.FStar_Syntax_Syntax.n in
                 match uu____3363 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3379 -> aux true t1'
                 | uu____3386 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3401 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3446 =
                   let uu____3447 = FStar_Syntax_Subst.compress t1' in
                   uu____3447.FStar_Syntax_Syntax.n in
                 match uu____3446 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3462 -> aux true t1'
                 | uu____3469 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3484 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3499 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3514 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3529 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3544 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3573 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3606 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3627 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3654 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3681 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3718 ->
              let uu____3725 =
                let uu____3726 = FStar_Syntax_Print.term_to_string t12 in
                let uu____3727 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3726 uu____3727 in
              failwith uu____3725
          | FStar_Syntax_Syntax.Tm_ascribed uu____3740 ->
              let uu____3767 =
                let uu____3768 = FStar_Syntax_Print.term_to_string t12 in
                let uu____3769 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3768 uu____3769 in
              failwith uu____3767
          | FStar_Syntax_Syntax.Tm_delayed uu____3782 ->
              let uu____3797 =
                let uu____3798 = FStar_Syntax_Print.term_to_string t12 in
                let uu____3799 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3798 uu____3799 in
              failwith uu____3797
          | FStar_Syntax_Syntax.Tm_unknown ->
              let uu____3812 =
                let uu____3813 = FStar_Syntax_Print.term_to_string t12 in
                let uu____3814 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3813 uu____3814 in
              failwith uu____3812 in
        let uu____3827 = whnf env t1 in aux false uu____3827
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env -> fun t -> base_and_refinement_maybe_delta false env t
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env ->
    fun t ->
      let uu____3868 = base_and_refinement env t in
      FStar_All.pipe_right uu____3868 FStar_Pervasives_Native.fst
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t ->
    let uu____3908 = FStar_Syntax_Syntax.null_bv t in
    (uu____3908, FStar_Syntax_Util.t_true)
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta ->
    fun env ->
      fun t ->
        let uu____3932 = base_and_refinement_maybe_delta delta env t in
        match uu____3932 with
        | (t_base, refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x, phi) -> (x, phi))
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____3991 ->
    match uu____3991 with
    | (t_base, refopt) ->
        let uu____4022 =
          match refopt with
          | FStar_Pervasives_Native.Some (y, phi) -> (y, phi)
          | FStar_Pervasives_Native.None -> trivial_refinement t_base in
        (match uu____4022 with
         | (y, phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl -> fun prob -> prob_to_string wl.tcenv prob
let (wl_to_string : worklist -> Prims.string) =
  fun wl ->
    let uu____4060 =
      let uu____4063 =
        let uu____4066 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4089 ->
                  match uu____4089 with | (uu____4096, uu____4097, x) -> x)) in
        FStar_List.append wl.attempting uu____4066 in
      FStar_List.map (wl_prob_to_string wl) uu____4063 in
    FStar_All.pipe_right uu____4060 (FStar_String.concat "\n\t")
type flex_t =
  | Flex of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
  FStar_Syntax_Syntax.args) 
let (uu___is_Flex : flex_t -> Prims.bool) = fun projectee -> true
let (__proj__Flex__item___0 :
  flex_t ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
      FStar_Syntax_Syntax.args))
  = fun projectee -> match projectee with | Flex _0 -> _0
let (flex_reason : flex_t -> Prims.string) =
  fun uu____4145 ->
    match uu____4145 with
    | Flex (uu____4146, u, uu____4148) ->
        u.FStar_Syntax_Syntax.ctx_uvar_reason
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4153 ->
    match uu____4153 with
    | Flex (uu____4154, c, args) ->
        let uu____4157 = print_ctx_uvar c in
        let uu____4158 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "%s [%s]" uu____4157 uu____4158
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____4164 = FStar_Syntax_Util.head_and_args t in
    match uu____4164 with
    | (head, _args) ->
        let uu____4207 =
          let uu____4208 = FStar_Syntax_Subst.compress head in
          uu____4208.FStar_Syntax_Syntax.n in
        (match uu____4207 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4211 -> true
         | uu____4224 -> false)
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t ->
    let uu____4230 = FStar_Syntax_Util.head_and_args t in
    match uu____4230 with
    | (head, _args) ->
        let uu____4273 =
          let uu____4274 = FStar_Syntax_Subst.compress head in
          uu____4274.FStar_Syntax_Syntax.n in
        (match uu____4273 with
         | FStar_Syntax_Syntax.Tm_uvar (u, uu____4278) -> u
         | uu____4295 -> failwith "Not a flex-uvar")
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0 ->
    fun wl ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x in
        let t_x' = FStar_Syntax_Subst.subst' s t_x in
        let uu____4327 =
          let uu____4328 = FStar_Syntax_Subst.compress t_x' in
          uu____4328.FStar_Syntax_Syntax.n in
        match uu____4327 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____4332 -> false in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____4345 -> true in
      let uu____4346 = FStar_Syntax_Util.head_and_args t0 in
      match uu____4346 with
      | (head, args) ->
          let uu____4393 =
            let uu____4394 = FStar_Syntax_Subst.compress head in
            uu____4394.FStar_Syntax_Syntax.n in
          (match uu____4393 with
           | FStar_Syntax_Syntax.Tm_uvar (uv, ([], uu____4402)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv, uu____4418) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
               let uu____4459 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma in
               (match uu____4459 with
                | (gamma_aff, new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____4486 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff in
                         let uu____4490 =
                           let uu____4497 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma in
                           let uu____4506 =
                             let uu____4509 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                             FStar_Syntax_Util.arrow dom_binders uu____4509 in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____4497
                             uu____4506
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta in
                         (match uu____4490 with
                          | (v, t_v, wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____4544 ->
                                     match uu____4544 with
                                     | (x, i) ->
                                         let uu____4563 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         (uu____4563, i)) dom_binders in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  t0.FStar_Syntax_Syntax.pos in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____4593 ->
                                       match uu____4593 with
                                       | (a, i) ->
                                           let uu____4612 =
                                             FStar_Syntax_Subst.subst' s a in
                                           (uu____4612, i)) args_sol in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    t0.FStar_Syntax_Syntax.pos in
                                (t, wl1))))))
           | uu____4622 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t ->
    let uu____4632 = FStar_Syntax_Util.head_and_args t in
    match uu____4632 with
    | (head, args) ->
        let uu____4675 =
          let uu____4676 = FStar_Syntax_Subst.compress head in
          uu____4676.FStar_Syntax_Syntax.n in
        (match uu____4675 with
         | FStar_Syntax_Syntax.Tm_uvar (uv, s) -> Flex (t, uv, args)
         | uu____4697 -> failwith "Not a flex-uvar")
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t ->
    fun wl ->
      let uu____4716 = ensure_no_uvar_subst t wl in
      match uu____4716 with
      | (t1, wl1) ->
          let uu____4727 = destruct_flex_t' t1 in (uu____4727, wl1)
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k ->
    fun ys ->
      fun t ->
        let uu____4743 =
          let uu____4766 =
            let uu____4767 = FStar_Syntax_Subst.compress k in
            uu____4767.FStar_Syntax_Syntax.n in
          match uu____4766 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4848 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____4848)
              else
                (let uu____4882 = FStar_Syntax_Util.abs_formals t in
                 match uu____4882 with
                 | (ys', t1, uu____4915) ->
                     let uu____4920 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____4920))
          | uu____4959 ->
              let uu____4960 =
                let uu____4965 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____4965) in
              ((ys, t), uu____4960) in
        match uu____4743 with
        | ((ys1, t1), (xs, c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____5058 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____5058 c in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok ->
    fun prob ->
      fun logical_guard ->
        fun uvis ->
          fun wl ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi in
             let assign_solution xs uv phi1 =
               (let uu____5132 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel") in
                if uu____5132
                then
                  let uu____5133 = FStar_Util.string_of_int (p_pid prob) in
                  let uu____5134 = print_ctx_uvar uv in
                  let uu____5135 = FStar_Syntax_Print.term_to_string phi1 in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5133 uu____5134 uu____5135
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0)) in
                (let uu____5141 =
                   let uu____5142 = FStar_Util.string_of_int (p_pid prob) in
                   Prims.op_Hat "solve_prob'.sol." uu____5142 in
                 let uu____5143 =
                   let uu____5146 = p_scope prob in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5146 in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5141 uu____5143 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2) in
             let uv = p_guard_uvar prob in
             let fail uu____5179 =
               let uu____5180 =
                 let uu____5181 = FStar_Syntax_Print.ctx_uvar_to_string uv in
                 let uu____5182 =
                   FStar_Syntax_Print.term_to_string (p_guard prob) in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5181 uu____5182 in
               failwith uu____5180 in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5246 ->
                       match uu____5246 with
                       | (a, i) ->
                           let uu____5267 =
                             let uu____5268 = FStar_Syntax_Subst.compress a in
                             uu____5268.FStar_Syntax_Syntax.n in
                           (match uu____5267 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5294 -> (fail (); [])))) in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob) in
               let uu____5304 =
                 let uu____5305 = is_flex g in Prims.op_Negation uu____5305 in
               if uu____5304
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____5309 = destruct_flex_t g wl in
                  match uu____5309 with
                  | (Flex (uu____5314, uv1, args), wl1) ->
                      ((let uu____5319 = args_as_binders args in
                        assign_solution uu____5319 uv1 phi);
                       wl1)) in
             commit uvis;
             (let uu___762_5321 = wl1 in
              {
                attempting = (uu___762_5321.attempting);
                wl_deferred = (uu___762_5321.wl_deferred);
                wl_deferred_to_tac = (uu___762_5321.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___762_5321.defer_ok);
                smt_ok = (uu___762_5321.smt_ok);
                umax_heuristic_ok = (uu___762_5321.umax_heuristic_ok);
                tcenv = (uu___762_5321.tcenv);
                wl_implicits = (uu___762_5321.wl_implicits);
                repr_subcomp_allowed = (uu___762_5321.repr_subcomp_allowed)
              }))
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid ->
    fun sol ->
      fun wl ->
        (let uu____5342 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel") in
         if uu____5342
         then
           let uu____5343 = FStar_Util.string_of_int pid in
           let uu____5344 = uvis_to_string wl.tcenv sol in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5343 uu____5344
         else ());
        commit sol;
        (let uu___770_5347 = wl in
         {
           attempting = (uu___770_5347.attempting);
           wl_deferred = (uu___770_5347.wl_deferred);
           wl_deferred_to_tac = (uu___770_5347.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___770_5347.defer_ok);
           smt_ok = (uu___770_5347.smt_ok);
           umax_heuristic_ok = (uu___770_5347.umax_heuristic_ok);
           tcenv = (uu___770_5347.tcenv);
           wl_implicits = (uu___770_5347.wl_implicits);
           repr_subcomp_allowed = (uu___770_5347.repr_subcomp_allowed)
         })
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob ->
    fun logical_guard ->
      fun uvis ->
        fun wl ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let uu____5379 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel") in
           if uu____5379
           then
             let uu____5380 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____5381 = uvis_to_string wl.tcenv uvis in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5380 uu____5381
           else ());
          solve_prob' false prob logical_guard uvis wl
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk ->
    fun t ->
      let uvars =
        let uu____5402 = FStar_Syntax_Free.uvars t in
        FStar_All.pipe_right uu____5402 FStar_Util.set_elements in
      let occurs =
        FStar_All.pipe_right uvars
          (FStar_Util.for_some
             (fun uv ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head)) in
      (uvars, occurs)
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
        FStar_Pervasives_Native.option))
  =
  fun uk ->
    fun t ->
      let uu____5436 = occurs uk t in
      match uu____5436 with
      | (uvars, occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5465 =
                 let uu____5466 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head in
                 let uu____5467 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5466 uu____5467 in
               FStar_Pervasives_Native.Some uu____5465) in
          (uvars, (Prims.op_Negation occurs1), msg)
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders *
        FStar_Syntax_Syntax.binders)))
  =
  fun bs ->
    fun bs' ->
      match (bs, bs') with
      | ((b, i)::bs_tail, (b', i')::bs'_tail) ->
          let uu____5572 = FStar_Syntax_Syntax.bv_eq b b' in
          if uu____5572
          then
            let uu____5581 = maximal_prefix bs_tail bs'_tail in
            (match uu____5581 with | (pfx, rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5631 -> ([], (bs, bs'))
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      FStar_List.fold_left
        (fun g1 ->
           fun uu____5687 ->
             match uu____5687 with
             | (x, uu____5699) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      let uu____5716 = FStar_List.last bs in
      match uu____5716 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some (x, uu____5740) ->
          let uu____5751 =
            FStar_Util.prefix_until
              (fun uu___18_5766 ->
                 match uu___18_5766 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5768 -> false) g in
          (match uu____5751 with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some (uu____5781, bx, rest) -> bx ::
               rest)
let (restrict_ctx :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun env ->
    fun tgt ->
      fun bs ->
        fun src ->
          fun wl ->
            let uu____5827 =
              maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
                src.FStar_Syntax_Syntax.ctx_uvar_binders in
            match uu____5827 with
            | (pfx, uu____5837) ->
                let g =
                  gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx in
                let aux t f =
                  let uu____5865 =
                    let uu____5872 =
                      let uu____5873 =
                        FStar_Syntax_Print.uvar_to_string
                          src.FStar_Syntax_Syntax.ctx_uvar_head in
                      Prims.op_Hat "restricted " uu____5873 in
                    new_uvar uu____5872 wl
                      src.FStar_Syntax_Syntax.ctx_uvar_range g pfx t
                      src.FStar_Syntax_Syntax.ctx_uvar_should_check
                      src.FStar_Syntax_Syntax.ctx_uvar_meta in
                  match uu____5865 with
                  | (uu____5874, src', wl1) ->
                      ((let uu____5878 = f src' in
                        FStar_Syntax_Util.set_uvar
                          src.FStar_Syntax_Syntax.ctx_uvar_head uu____5878);
                       wl1) in
                let bs1 =
                  FStar_All.pipe_right bs
                    (FStar_List.filter
                       (fun uu____5913 ->
                          match uu____5913 with
                          | (bv1, uu____5921) ->
                              FStar_List.existsb
                                (fun uu____5935 ->
                                   match uu____5935 with
                                   | (bv2, uu____5943) ->
                                       FStar_Syntax_Syntax.bv_eq bv1 bv2)
                                src.FStar_Syntax_Syntax.ctx_uvar_binders)) in
                if (FStar_List.length bs1) = Prims.int_zero
                then
                  aux src.FStar_Syntax_Syntax.ctx_uvar_typ (fun src' -> src')
                else
                  (let uu____5957 =
                     let uu____5958 =
                       let uu____5961 =
                         let uu____5964 =
                           FStar_All.pipe_right
                             src.FStar_Syntax_Syntax.ctx_uvar_typ
                             (env.FStar_TypeChecker_Env.universe_of env) in
                         FStar_All.pipe_right uu____5964
                           (fun uu____5967 ->
                              FStar_Pervasives_Native.Some uu____5967) in
                       FStar_All.pipe_right uu____5961
                         (FStar_Syntax_Syntax.mk_Total'
                            src.FStar_Syntax_Syntax.ctx_uvar_typ) in
                     FStar_All.pipe_right uu____5958
                       (FStar_Syntax_Util.arrow bs1) in
                   aux uu____5957
                     (fun src' ->
                        let uu____5977 =
                          let uu____5978 =
                            let uu____5995 =
                              let uu____6006 =
                                let uu____6009 =
                                  FStar_All.pipe_right bs1
                                    (FStar_List.map
                                       FStar_Pervasives_Native.fst) in
                                FStar_All.pipe_right uu____6009
                                  (FStar_List.map
                                     FStar_Syntax_Syntax.bv_to_name) in
                              FStar_All.pipe_right uu____6006
                                (FStar_List.map FStar_Syntax_Syntax.as_arg) in
                            (src', uu____5995) in
                          FStar_Syntax_Syntax.Tm_app uu____5978 in
                        FStar_Syntax_Syntax.mk uu____5977
                          src.FStar_Syntax_Syntax.ctx_uvar_range))
let (restrict_all_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun env ->
    fun tgt ->
      fun bs ->
        fun sources ->
          fun wl ->
            FStar_List.fold_right (restrict_ctx env tgt bs) sources wl
let (intersect_binders :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun g ->
    fun v1 ->
      fun v2 ->
        let as_set v =
          FStar_All.pipe_right v
            (FStar_List.fold_left
               (fun out ->
                  fun x ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names) in
        let v1_set = as_set v1 in
        let ctx_binders =
          FStar_List.fold_left
            (fun out ->
               fun b ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____6176 -> out) FStar_Syntax_Syntax.no_names g in
        let uu____6177 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6241 ->
                  fun uu____6242 ->
                    match (uu____6241, uu____6242) with
                    | ((isect, isect_set), (x, imp)) ->
                        let uu____6345 =
                          let uu____6346 = FStar_Util.set_mem x v1_set in
                          FStar_All.pipe_left Prims.op_Negation uu____6346 in
                        if uu____6345
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6375 =
                             FStar_Util.set_is_subset_of fvs isect_set in
                           if uu____6375
                           then
                             let uu____6390 = FStar_Util.set_add x isect_set in
                             (((x, imp) :: isect), uu____6390)
                           else (isect, isect_set))) ([], ctx_binders)) in
        match uu____6177 with | (isect, uu____6439) -> FStar_List.rev isect
let binders_eq :
  'uuuuuu6474 'uuuuuu6475 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6474) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6475) Prims.list -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6532 ->
              fun uu____6533 ->
                match (uu____6532, uu____6533) with
                | ((a, uu____6551), (b, uu____6553)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let name_exists_in_binders :
  'uuuuuu6568 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6568) Prims.list -> Prims.bool
  =
  fun x ->
    fun bs ->
      FStar_Util.for_some
        (fun uu____6598 ->
           match uu____6598 with
           | (y, uu____6604) -> FStar_Syntax_Syntax.bv_eq x y) bs
let pat_vars :
  'uuuuuu6613 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6613) Prims.list ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list ->
          FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env ->
    fun ctx ->
      fun args ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
          | (arg, i)::args2 ->
              let hd = sn env arg in
              (match hd.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____6775 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu____6775
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6805 -> FStar_Pervasives_Native.None) in
        aux [] args
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu____6852 -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch _0 -> true | uu____6889 -> false
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee -> match projectee with | HeadMatch _0 -> _0
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | FullMatch -> true | uu____6901 -> false
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_6906 ->
    match uu___19_6906 with
    | MisMatch (d1, d2) ->
        let uu____6917 =
          let uu____6918 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu____6919 =
            let uu____6920 =
              let uu____6921 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.op_Hat uu____6921 ")" in
            Prims.op_Hat ") (" uu____6920 in
          Prims.op_Hat uu____6918 uu____6919 in
        Prims.op_Hat "MisMatch (" uu____6917
    | HeadMatch u ->
        let uu____6923 = FStar_Util.string_of_bool u in
        Prims.op_Hat "HeadMatch " uu____6923
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___20_6928 ->
    match uu___20_6928 with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu____6943 -> HeadMatch false
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____6956 =
            (let uu____6961 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
             let uu____6962 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu____6961 = uu____6962) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) in
          if uu____6956 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____6965 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6965 with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6976 -> d)
      | d1 -> d1
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____6999 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7008 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7026 = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu____7026
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7027 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7028 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7029 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7042 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7055 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____7079) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____7085, uu____7086) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu____7128) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7153;
             FStar_Syntax_Syntax.index = uu____7154;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____7156)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7163 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7164 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7165 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7180 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7187 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7207 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____7207
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let t11 = FStar_Syntax_Util.unmeta t1 in
        let t21 = FStar_Syntax_Util.unmeta t2 in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7225;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7226;
             FStar_Syntax_Syntax.ltyp = uu____7227;
             FStar_Syntax_Syntax.rng = uu____7228;_},
           uu____7229) ->
            let uu____7240 = FStar_Syntax_Util.unlazy t11 in
            head_matches env uu____7240 t21
        | (uu____7241, FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7242;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7243;
             FStar_Syntax_Syntax.ltyp = uu____7244;
             FStar_Syntax_Syntax.rng = uu____7245;_})
            ->
            let uu____7256 = FStar_Syntax_Util.unlazy t21 in
            head_matches env t11 uu____7256
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7259 = FStar_Syntax_Syntax.bv_eq x y in
            if uu____7259
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7267 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____7267
            then FullMatch
            else
              (let uu____7269 =
                 let uu____7278 =
                   let uu____7281 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____7281 in
                 let uu____7282 =
                   let uu____7285 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____7285 in
                 (uu____7278, uu____7282) in
               MisMatch uu____7269)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu____7291),
           FStar_Syntax_Syntax.Tm_uinst (g, uu____7293)) ->
            let uu____7302 = head_matches env f g in
            FStar_All.pipe_right uu____7302 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           uu____7303) -> HeadMatch true
        | (uu____7304, FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify)) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7307 = FStar_Const.eq_const c d in
            if uu____7307
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu____7314),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu____7316)) ->
            let uu____7349 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head in
            if uu____7349
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7356),
           FStar_Syntax_Syntax.Tm_refine (y, uu____7358)) ->
            let uu____7367 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7367 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7369), uu____7370) ->
            let uu____7375 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____7375 head_match
        | (uu____7376, FStar_Syntax_Syntax.Tm_refine (x, uu____7378)) ->
            let uu____7383 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7383 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7384,
           FStar_Syntax_Syntax.Tm_type uu____7385) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow uu____7386,
           FStar_Syntax_Syntax.Tm_arrow uu____7387) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7417),
           FStar_Syntax_Syntax.Tm_app (head', uu____7419)) ->
            let uu____7468 = head_matches env head head' in
            FStar_All.pipe_right uu____7468 head_match
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7470), uu____7471) ->
            let uu____7496 = head_matches env head t21 in
            FStar_All.pipe_right uu____7496 head_match
        | (uu____7497, FStar_Syntax_Syntax.Tm_app (head, uu____7499)) ->
            let uu____7524 = head_matches env t11 head in
            FStar_All.pipe_right uu____7524 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7525, FStar_Syntax_Syntax.Tm_let
           uu____7526) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match uu____7551,
           FStar_Syntax_Syntax.Tm_match uu____7552) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7597, FStar_Syntax_Syntax.Tm_abs
           uu____7598) -> HeadMatch true
        | uu____7635 ->
            let uu____7640 =
              let uu____7649 = delta_depth_of_term env t11 in
              let uu____7652 = delta_depth_of_term env t21 in
              (uu____7649, uu____7652) in
            MisMatch uu____7640
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    worklist ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.option))
  =
  fun env ->
    fun wl ->
      fun t1 ->
        fun t2 ->
          let maybe_inline t =
            let head =
              let uu____7720 = unrefine env t in
              FStar_Syntax_Util.head_of uu____7720 in
            (let uu____7722 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7722
             then
               let uu____7723 = FStar_Syntax_Print.term_to_string t in
               let uu____7724 = FStar_Syntax_Print.term_to_string head in
               FStar_Util.print2 "Head of %s is %s\n" uu____7723 uu____7724
             else ());
            (let uu____7726 =
               let uu____7727 = FStar_Syntax_Util.un_uinst head in
               uu____7727.FStar_Syntax_Syntax.n in
             match uu____7726 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7733 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 (match uu____7733 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu____7747 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta") in
                        if uu____7747
                        then
                          let uu____7748 =
                            FStar_Syntax_Print.term_to_string head in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7748
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7750 ->
                      let basic_steps =
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF;
                        FStar_TypeChecker_Env.Primops;
                        FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.Iota] in
                      let steps =
                        if wl.smt_ok
                        then basic_steps
                        else
                          (FStar_TypeChecker_Env.Exclude
                             FStar_TypeChecker_Env.Zeta)
                          :: basic_steps in
                      let t' =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.1" steps env
                          t in
                      let uu____7765 =
                        let uu____7766 = FStar_Syntax_Util.eq_tm t t' in
                        uu____7766 = FStar_Syntax_Util.Equal in
                      if uu____7765
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7771 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta") in
                          if uu____7771
                          then
                            let uu____7772 =
                              FStar_Syntax_Print.term_to_string t in
                            let uu____7773 =
                              FStar_Syntax_Print.term_to_string t' in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7772
                              uu____7773
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7775 -> FStar_Pervasives_Native.None) in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None)) in
          let fail d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None)) in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21 in
            (let uu____7913 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7913
             then
               let uu____7914 = FStar_Syntax_Print.term_to_string t11 in
               let uu____7915 = FStar_Syntax_Print.term_to_string t21 in
               let uu____7916 = string_of_match_result r in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7914
                 uu____7915 uu____7916
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
               let uu____7940 =
                 if d1_greater_than_d2
                 then
                   let t1' =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d2;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11 in
                   (t1', t21)
                 else
                   (let t2' =
                      normalize_refinement
                        [FStar_TypeChecker_Env.UnfoldUntil d1;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF] env t21 in
                    (t11, t2')) in
               match uu____7940 with
               | (t12, t22) -> aux retry (n_delta + Prims.int_one) t12 t22 in
             let reduce_both_and_try_again d r1 =
               let uu____7985 = FStar_TypeChecker_Common.decr_delta_depth d in
               match uu____7985 with
               | FStar_Pervasives_Native.None -> fail n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t12 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11 in
                   let t22 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t21 in
                   aux retry (n_delta + Prims.int_one) t12 t22 in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level i),
                  FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > Prims.int_zero) || (j > Prims.int_zero)) && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8017),
                  uu____8018)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8036 =
                      let uu____8045 = maybe_inline t11 in
                      let uu____8048 = maybe_inline t21 in
                      (uu____8045, uu____8048) in
                    match uu____8036 with
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) ->
                        fail n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some t12,
                       FStar_Pervasives_Native.None) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some t12,
                       FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (uu____8085, FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8086))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8104 =
                      let uu____8113 = maybe_inline t11 in
                      let uu____8116 = maybe_inline t21 in
                      (uu____8113, uu____8116) in
                    match uu____8104 with
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) ->
                        fail n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some t12,
                       FStar_Pervasives_Native.None) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some t12,
                       FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some d1,
                  FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some d1,
                  FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____8165 -> fail n_delta r t11 t21
             | uu____8174 -> success n_delta r t11 t21) in
          let r = aux true Prims.int_zero t1 t2 in
          (let uu____8187 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu____8187
           then
             let uu____8188 = FStar_Syntax_Print.term_to_string t1 in
             let uu____8189 = FStar_Syntax_Print.term_to_string t2 in
             let uu____8190 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             let uu____8197 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8209 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must in
                  FStar_All.pipe_right uu____8209
                    (fun uu____8243 ->
                       match uu____8243 with
                       | (t11, t21) ->
                           let uu____8250 =
                             FStar_Syntax_Print.term_to_string t11 in
                           let uu____8251 =
                             let uu____8252 =
                               FStar_Syntax_Print.term_to_string t21 in
                             Prims.op_Hat "; " uu____8252 in
                           Prims.op_Hat uu____8250 uu____8251)) in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8188 uu____8189 uu____8190 uu____8197
           else ());
          r
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____8264 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____8264 FStar_Pervasives_Native.fst
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8277 ->
    match uu___21_8277 with
    | FStar_TypeChecker_Common.Rigid_rigid -> Prims.int_zero
    | FStar_TypeChecker_Common.Flex_rigid_eq -> Prims.int_one
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq -> (Prims.of_int (2))
    | FStar_TypeChecker_Common.Flex_rigid -> (Prims.of_int (3))
    | FStar_TypeChecker_Common.Rigid_flex -> (Prims.of_int (4))
    | FStar_TypeChecker_Common.Flex_flex -> (Prims.of_int (5))
let (rank_leq :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1 -> fun r2 -> (rank_t_num r1) <= (rank_t_num r2)
let (rank_less_than :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1 -> fun r2 -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2))
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv ->
    fun p ->
      let uu___1276_8314 = p in
      let uu____8317 = whnf tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8318 = whnf tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1276_8314.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8317;
        FStar_TypeChecker_Common.relation =
          (uu___1276_8314.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8318;
        FStar_TypeChecker_Common.element =
          (uu___1276_8314.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1276_8314.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1276_8314.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1276_8314.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1276_8314.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1276_8314.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8332 = compress_tprob tcenv p1 in
          FStar_All.pipe_right uu____8332
            (fun uu____8337 -> FStar_TypeChecker_Common.TProb uu____8337)
      | FStar_TypeChecker_Common.CProb uu____8338 -> p
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv ->
    fun pr ->
      let prob =
        let uu____8360 = compress_prob tcenv pr in
        FStar_All.pipe_right uu____8360 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8368 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8368 with
           | (lh, lhs_args) ->
               let uu____8415 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8415 with
                | (rh, rhs_args) ->
                    let uu____8462 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8475,
                         FStar_Syntax_Syntax.Tm_uvar uu____8476) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8565 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8592, uu____8593)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8608, FStar_Syntax_Syntax.Tm_uvar uu____8609)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8624,
                         FStar_Syntax_Syntax.Tm_arrow uu____8625) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1327_8655 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1327_8655.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1327_8655.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1327_8655.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1327_8655.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1327_8655.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1327_8655.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1327_8655.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1327_8655.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1327_8655.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8658,
                         FStar_Syntax_Syntax.Tm_type uu____8659) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1327_8675 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1327_8675.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1327_8675.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1327_8675.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1327_8675.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1327_8675.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1327_8675.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1327_8675.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1327_8675.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1327_8675.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type uu____8678,
                         FStar_Syntax_Syntax.Tm_uvar uu____8679) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1327_8695 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1327_8695.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1327_8695.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1327_8695.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1327_8695.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1327_8695.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1327_8695.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1327_8695.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1327_8695.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1327_8695.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8698, FStar_Syntax_Syntax.Tm_uvar uu____8699)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8714, uu____8715)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8730, FStar_Syntax_Syntax.Tm_uvar uu____8731)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8746, uu____8747) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu____8462 with
                     | (rank, tp1) ->
                         let uu____8760 =
                           FStar_All.pipe_right
                             (let uu___1347_8764 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1347_8764.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1347_8764.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1347_8764.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1347_8764.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1347_8764.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1347_8764.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1347_8764.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1347_8764.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1347_8764.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____8767 ->
                                FStar_TypeChecker_Common.TProb uu____8767) in
                         (rank, uu____8760))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8771 =
            FStar_All.pipe_right
              (let uu___1351_8775 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1351_8775.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1351_8775.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1351_8775.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1351_8775.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1351_8775.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1351_8775.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1351_8775.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1351_8775.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1351_8775.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____8778 -> FStar_TypeChecker_Common.CProb uu____8778) in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8771)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    let rec aux uu____8837 probs =
      match uu____8837 with
      | (min_rank, min, out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some p,
                   FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8918 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____8939 = rank wl.tcenv hd in
               (match uu____8939 with
                | (rank1, hd1) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min with
                       | FStar_Pervasives_Native.None ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_List.append out tl), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_List.append out (m :: tl)), rank1))
                    else
                      (let uu____8998 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9002 = FStar_Option.get min_rank in
                            rank_less_than rank1 uu____9002) in
                       if uu____8998
                       then
                         match min with
                         | FStar_Pervasives_Native.None ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), out) tl
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), (m ::
                                 out)) tl
                       else aux (min_rank, min, (hd1 :: out)) tl))) in
    aux (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, [])
      wl.attempting
let (flex_prob_closing :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv ->
    fun bs ->
      fun p ->
        let flex_will_be_closed t =
          let uu____9070 = FStar_Syntax_Util.head_and_args t in
          match uu____9070 with
          | (hd, uu____9088) ->
              let uu____9113 =
                let uu____9114 = FStar_Syntax_Subst.compress hd in
                uu____9114.FStar_Syntax_Syntax.n in
              (match uu____9113 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu____9118) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9152 ->
                           match uu____9152 with
                           | (y, uu____9160) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9182 ->
                                       match uu____9182 with
                                       | (x, uu____9190) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9195 -> false) in
        let uu____9196 = rank tcenv p in
        match uu____9196 with
        | (r, p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9203 -> true
             | FStar_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStar_TypeChecker_Common.Rigid_rigid -> true
                  | FStar_TypeChecker_Common.Flex_rigid_eq -> true
                  | FStar_TypeChecker_Common.Flex_flex_pattern_eq -> true
                  | FStar_TypeChecker_Common.Flex_rigid ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                  | FStar_TypeChecker_Common.Rigid_flex ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.rhs
                  | FStar_TypeChecker_Common.Flex_flex ->
                      (p2.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                        &&
                        ((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
                           ||
                           (flex_will_be_closed
                              p2.FStar_TypeChecker_Common.rhs))))
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of lstring 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UDeferred _0 -> true | uu____9235 -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | USolved _0 -> true | uu____9248 -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UFailed _0 -> true | uu____9261 -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s -> let uu____9273 = FStar_Thunk.mkv s in UFailed uu____9273
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu____9284 = mklstr s in UFailed uu____9284
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig ->
    fun wl ->
      fun u1 ->
        fun u2 ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1 in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2 in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3 ->
                        let uu____9329 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____9329 with
                        | (k, uu____9335) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9347 -> false)))
            | uu____9348 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu____9400 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2 -> FStar_Syntax_Util.eq_univs uv1 uv2)) in
                        if uu____9400 then uv1 :: uvs else uvs) []) in
            let filter =
              FStar_List.filter
                (fun u ->
                   let uu____9420 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u' -> FStar_Syntax_Util.eq_univs u u')) in
                   Prims.op_Negation uu____9420) in
            let uu____9425 = filter u12 in
            let uu____9428 = filter u22 in (uu____9425, uu____9428) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9458 = filter_out_common_univs us1 us2 in
                   (match uu____9458 with
                    | (us11, us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13, u23::us23) ->
                                let uu____9517 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23 in
                                (match uu____9517 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9520 -> USolved wl1 in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9536 ->
                               let uu____9537 =
                                 FStar_Syntax_Print.univ_to_string u12 in
                               let uu____9538 =
                                 FStar_Syntax_Print.univ_to_string u22 in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9537 uu____9538))
               | (FStar_Syntax_Syntax.U_max us, u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9562 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9562 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | (u', FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9588 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9588 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | uu____9591 ->
                   ufailed_thunk
                     (fun uu____9602 ->
                        let uu____9603 =
                          FStar_Syntax_Print.univ_to_string u12 in
                        let uu____9604 =
                          FStar_Syntax_Print.univ_to_string u22 in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____9603 uu____9604 msg)) in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9605, uu____9606) ->
              let uu____9607 =
                let uu____9608 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9609 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9608 uu____9609 in
              failwith uu____9607
          | (FStar_Syntax_Syntax.U_unknown, uu____9610) ->
              let uu____9611 =
                let uu____9612 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9613 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9612 uu____9613 in
              failwith uu____9611
          | (uu____9614, FStar_Syntax_Syntax.U_bvar uu____9615) ->
              let uu____9616 =
                let uu____9617 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9618 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9617 uu____9618 in
              failwith uu____9616
          | (uu____9619, FStar_Syntax_Syntax.U_unknown) ->
              let uu____9620 =
                let uu____9621 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9622 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9621 uu____9622 in
              failwith uu____9620
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              let uu____9625 =
                let uu____9626 = FStar_Ident.string_of_id x in
                let uu____9627 = FStar_Ident.string_of_id y in
                uu____9626 = uu____9627 in
              if uu____9625
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9653 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9653
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu____9669 = occurs_univ v1 u3 in
              if uu____9669
              then
                let uu____9670 =
                  let uu____9671 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9672 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9671 uu____9672 in
                try_umax_components u11 u21 uu____9670
              else
                (let uu____9674 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9674)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9688 = occurs_univ v1 u3 in
              if uu____9688
              then
                let uu____9689 =
                  let uu____9690 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9691 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9690 uu____9691 in
                try_umax_components u11 u21 uu____9689
              else
                (let uu____9693 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9693)
          | (FStar_Syntax_Syntax.U_max uu____9694, uu____9695) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9701 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9701
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9703, FStar_Syntax_Syntax.U_max uu____9704) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9710 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9710
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9712,
             FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9713,
             FStar_Syntax_Syntax.U_name uu____9714) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ
             uu____9715) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name
             uu____9716) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9717,
             FStar_Syntax_Syntax.U_succ uu____9718) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9719,
             FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig ->
    fun wl ->
      fun u1 ->
        fun u2 ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
let match_num_binders :
  'a 'b .
    ('a Prims.list * ('a Prims.list -> 'b)) ->
      ('a Prims.list * ('a Prims.list -> 'b)) ->
        (('a Prims.list * 'b) * ('a Prims.list * 'b))
  =
  fun bc1 ->
    fun bc2 ->
      let uu____9819 = bc1 in
      match uu____9819 with
      | (bs1, mk_cod1) ->
          let uu____9863 = bc2 in
          (match uu____9863 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu____9974 = aux xs ys in
                     (match uu____9974 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu____10057 =
                       let uu____10064 = mk_cod1 xs in ([], uu____10064) in
                     let uu____10067 =
                       let uu____10074 = mk_cod2 ys in ([], uu____10074) in
                     (uu____10057, uu____10067) in
               aux bs1 bs2)
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun env ->
    fun wl ->
      fun problem ->
        fun t1 ->
          fun t2 ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  let uu____10142 = FStar_Syntax_Syntax.bv_to_name t in
                  FStar_Syntax_Util.mk_has_type t11 uu____10142 t21
              | FStar_Pervasives_Native.None ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11 in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11 in
                  let uu____10145 =
                    let uu____10146 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Util.mk_has_type t11 uu____10146 t21 in
                  FStar_Syntax_Util.mk_forall u_x x uu____10145 in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB ->
                let uu____10151 = has_type_guard t1 t2 in (uu____10151, wl)
            | FStar_TypeChecker_Common.SUBINV ->
                let uu____10152 = has_type_guard t2 t1 in (uu____10152, wl)
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_10157 ->
    match uu___22_10157 with
    | Flex (uu____10158, uu____10159, []) -> true
    | uu____10168 -> false
let (should_defer_flex_to_user_tac :
  FStar_TypeChecker_Env.env -> worklist -> flex_t -> Prims.bool) =
  fun env ->
    fun wl ->
      fun f ->
        let uu____10184 = f in
        match uu____10184 with
        | Flex (uu____10185, u, uu____10187) ->
            let b =
              FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                wl.tcenv u in
            ((let uu____10190 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ResolveImplicitsHook") in
              if uu____10190
              then
                let uu____10191 =
                  FStar_Syntax_Print.ctx_uvar_to_string_no_reason u in
                let uu____10192 = FStar_Util.string_of_bool b in
                FStar_Util.print2
                  "Rel.should_defer_flex_to_user_tac for %s returning %s\n"
                  uu____10191 uu____10192
              else ());
             b)
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env ->
    fun f ->
      let uu____10216 = f in
      match uu____10216 with
      | Flex
          (uu____10223,
           { FStar_Syntax_Syntax.ctx_uvar_head = uu____10224;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10225;
             FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
             FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____10228;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____10229;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____10230;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____10231;_},
           args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10295 ->
                 match uu____10295 with
                 | (y, uu____10303) -> FStar_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu____10457 =
                  let uu____10472 =
                    let uu____10475 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10475 in
                  ((FStar_List.rev pat_binders), uu____10472) in
                FStar_Pervasives_Native.Some uu____10457
            | (uu____10508, []) ->
                let uu____10539 =
                  let uu____10554 =
                    let uu____10557 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10557 in
                  ((FStar_List.rev pat_binders), uu____10554) in
                FStar_Pervasives_Native.Some uu____10539
            | ((formal, formal_imp)::formals1, (a, a_imp)::args2) ->
                let uu____10648 =
                  let uu____10649 = FStar_Syntax_Subst.compress a in
                  uu____10649.FStar_Syntax_Syntax.n in
                (match uu____10648 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____10669 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders) in
                     if uu____10669
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1692_10696 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1692_10696.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1692_10696.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          } in
                        let subst =
                          let uu____10700 =
                            let uu____10701 =
                              let uu____10708 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              (formal, uu____10708) in
                            FStar_Syntax_Syntax.NT uu____10701 in
                          [uu____10700] in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1 in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res in
                        aux
                          (((let uu___1698_10724 = x1 in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1698_10724.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1698_10724.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10725 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([], args2) ->
                let uu____10765 =
                  let uu____10772 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStar_Syntax_Util.arrow_formals uu____10772 in
                (match uu____10765 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10831 ->
                          aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10856 ->
               let uu____10857 = FStar_Syntax_Util.arrow_formals t_hd in
               (match uu____10857 with
                | (formals, t_res) -> aux [] formals t_res args))
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu____11186 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel") in
       if uu____11186
       then
         let uu____11187 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11187
       else ());
      (let uu____11190 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace") in
       if uu____11190
       then
         let uu____11191 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11191
       else ());
      (let uu____11193 = next_prob probs in
       match uu____11193 with
       | FStar_Pervasives_Native.Some (hd, tl, rank1) ->
           let probs1 =
             let uu___1725_11220 = probs in
             {
               attempting = tl;
               wl_deferred = (uu___1725_11220.wl_deferred);
               wl_deferred_to_tac = (uu___1725_11220.wl_deferred_to_tac);
               ctr = (uu___1725_11220.ctr);
               defer_ok = (uu___1725_11220.defer_ok);
               smt_ok = (uu___1725_11220.smt_ok);
               umax_heuristic_ok = (uu___1725_11220.umax_heuristic_ok);
               tcenv = (uu___1725_11220.tcenv);
               wl_implicits = (uu___1725_11220.wl_implicits);
               repr_subcomp_allowed = (uu___1725_11220.repr_subcomp_allowed)
             } in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11228 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs in
                 if uu____11228
                 then
                   let uu____11229 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                   solve env uu____11229
                 else
                   if
                     (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                       ((tp.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                          && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                   then solve_t env tp probs1
                   else
                     if probs1.defer_ok
                     then
                       maybe_defer_to_user_tac env tp
                         "deferring flex_rigid or flex_flex subtyping" probs1
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1737_11234 = tp in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1737_11234.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1737_11234.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1737_11234.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1737_11234.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1737_11234.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1737_11234.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1737_11234.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1737_11234.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1737_11234.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None ->
           (match probs.wl_deferred with
            | [] ->
                let uu____11252 =
                  let uu____11259 = as_deferred probs.wl_deferred_to_tac in
                  ([], uu____11259, (probs.wl_implicits)) in
                Success uu____11252
            | uu____11264 ->
                let uu____11273 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11332 ->
                          match uu____11332 with
                          | (c, uu____11340, uu____11341) -> c < probs.ctr)) in
                (match uu____11273 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11382 =
                            let uu____11389 = as_deferred probs.wl_deferred in
                            let uu____11390 =
                              as_deferred probs.wl_deferred_to_tac in
                            (uu____11389, uu____11390, (probs.wl_implicits)) in
                          Success uu____11382
                      | uu____11391 ->
                          let uu____11400 =
                            let uu___1751_11401 = probs in
                            let uu____11402 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11421 ->
                                      match uu____11421 with
                                      | (uu____11428, uu____11429, y) -> y)) in
                            {
                              attempting = uu____11402;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1751_11401.wl_deferred_to_tac);
                              ctr = (uu___1751_11401.ctr);
                              defer_ok = (uu___1751_11401.defer_ok);
                              smt_ok = (uu___1751_11401.smt_ok);
                              umax_heuristic_ok =
                                (uu___1751_11401.umax_heuristic_ok);
                              tcenv = (uu___1751_11401.tcenv);
                              wl_implicits = (uu___1751_11401.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1751_11401.repr_subcomp_allowed)
                            } in
                          solve env uu____11400))))
and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env ->
    fun orig ->
      fun u1 ->
        fun u2 ->
          fun wl ->
            let uu____11436 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____11436 with
            | USolved wl1 ->
                let uu____11438 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____11438
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11441 = defer_lit "" orig wl1 in
                solve env uu____11441
and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env ->
    fun orig ->
      fun t1 ->
        fun t2 ->
          fun wl ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([], []) -> USolved wl1
              | (u1::us11, u2::us21) ->
                  let uu____11491 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____11491 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11494 -> ufailed_simple "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11506;
                  FStar_Syntax_Syntax.vars = uu____11507;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11510;
                  FStar_Syntax_Syntax.vars = uu____11511;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11523, uu____11524) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11531, FStar_Syntax_Syntax.Tm_uinst uu____11532) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11539 -> USolved wl
and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> lstring -> solution)
  =
  fun env ->
    fun orig ->
      fun wl ->
        fun msg ->
          if wl.defer_ok
          then
            ((let uu____11549 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____11549
              then
                let uu____11550 = prob_to_string env orig in
                let uu____11551 = FStar_Thunk.force msg in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11550 uu____11551
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and (defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> worklist -> solution)
  =
  fun env ->
    fun orig ->
      fun reason ->
        fun wl ->
          (let uu____11559 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____11559
           then
             let uu____11560 = prob_to_string env orig in
             FStar_Util.print1 "\n\t\tDeferring %s to a tactic\n" uu____11560
           else ());
          (let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
           let wl2 =
             let uu___1835_11564 = wl1 in
             let uu____11565 =
               let uu____11574 =
                 let uu____11581 = FStar_Thunk.mkv reason in
                 ((wl1.ctr), uu____11581, orig) in
               uu____11574 :: (wl1.wl_deferred_to_tac) in
             {
               attempting = (uu___1835_11564.attempting);
               wl_deferred = (uu___1835_11564.wl_deferred);
               wl_deferred_to_tac = uu____11565;
               ctr = (uu___1835_11564.ctr);
               defer_ok = (uu___1835_11564.defer_ok);
               smt_ok = (uu___1835_11564.smt_ok);
               umax_heuristic_ok = (uu___1835_11564.umax_heuristic_ok);
               tcenv = (uu___1835_11564.tcenv);
               wl_implicits = (uu___1835_11564.wl_implicits);
               repr_subcomp_allowed = (uu___1835_11564.repr_subcomp_allowed)
             } in
           solve env wl2)
and (maybe_defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem ->
      Prims.string -> worklist -> solution)
  =
  fun env ->
    fun prob ->
      fun reason ->
        fun wl ->
          match prob.FStar_TypeChecker_Common.relation with
          | FStar_TypeChecker_Common.EQ ->
              let should_defer_tac t =
                let uu____11604 = FStar_Syntax_Util.head_and_args t in
                match uu____11604 with
                | (head, uu____11626) ->
                    let uu____11651 =
                      let uu____11652 = FStar_Syntax_Subst.compress head in
                      uu____11652.FStar_Syntax_Syntax.n in
                    (match uu____11651 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu____11660) ->
                         let uu____11677 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu____11677,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____11678 -> (false, "")) in
              let uu____11679 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu____11679 with
               | (l1, r1) ->
                   let uu____11686 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu____11686 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____11694 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl in
                           solve env uu____11694)))
          | uu____11695 ->
              let uu____11696 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu____11696
and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)
  =
  fun rank1 ->
    fun env ->
      fun tp ->
        fun wl ->
          def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
            (FStar_TypeChecker_Common.TProb tp);
          (let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid in
           let meet_or_join op ts env1 wl1 =
             let eq_prob t1 t2 wl2 =
               let uu____11780 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu____11780 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu____11833 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu____11833
                then
                  let uu____11834 = FStar_Syntax_Print.term_to_string t1 in
                  let uu____11835 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____11834 uu____11835
                else ());
               (let uu____11837 = head_matches_delta env1 wl2 t1 t2 in
                match uu____11837 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu____11882 = eq_prob t1 t2 wl2 in
                         (match uu____11882 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11903 ->
                         let uu____11912 = eq_prob t1 t2 wl2 in
                         (match uu____11912 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu____11961 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu____11976 =
                                 FStar_Syntax_Subst.compress t11 in
                               let uu____11977 =
                                 FStar_Syntax_Subst.compress t21 in
                               (uu____11976, uu____11977)
                           | FStar_Pervasives_Native.None ->
                               let uu____11982 =
                                 FStar_Syntax_Subst.compress t1 in
                               let uu____11983 =
                                 FStar_Syntax_Subst.compress t2 in
                               (uu____11982, uu____11983) in
                         (match uu____11961 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12014 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu____12014 with
                                | (t1_hd, t1_args) ->
                                    let uu____12059 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu____12059 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12123 =
                                              let uu____12130 =
                                                let uu____12141 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu____12141 :: t1_args in
                                              let uu____12158 =
                                                let uu____12167 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu____12167 :: t2_args in
                                              FStar_List.fold_left2
                                                (fun uu____12216 ->
                                                   fun uu____12217 ->
                                                     fun uu____12218 ->
                                                       match (uu____12216,
                                                               uu____12217,
                                                               uu____12218)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu____12268),
                                                          (a2, uu____12270))
                                                           ->
                                                           let uu____12307 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu____12307
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12130
                                                uu____12158 in
                                            match uu____12123 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  let uu___1938_12333 = wl4 in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1938_12333.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1938_12333.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1938_12333.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1938_12333.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1938_12333.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____12341 =
                                                  solve env1 wl' in
                                                (match uu____12341 with
                                                 | Success
                                                     (uu____12344,
                                                      defer_to_tac, imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____12348 =
                                                         extend_wl wl4
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu____12348))
                                                 | Failed uu____12349 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu____12381 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu____12381 with
                                | (t1_base, p1_opt) ->
                                    let uu____12416 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu____12416 with
                                     | (t2_base, p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____12514 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu____12514
                                             then x.FStar_Syntax_Syntax.sort
                                             else
                                               FStar_Syntax_Util.refine x t in
                                           match (p1_opt1, p2_opt1) with
                                           | (FStar_Pervasives_Native.Some
                                              (x, phi1),
                                              FStar_Pervasives_Native.Some
                                              (y, phi2)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)] in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi1 in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi2 in
                                               let uu____12562 =
                                                 op phi11 phi21 in
                                               refine x1 uu____12562
                                           | (FStar_Pervasives_Native.None,
                                              FStar_Pervasives_Native.Some
                                              (x, phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)] in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi in
                                               let uu____12592 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12592
                                           | (FStar_Pervasives_Native.Some
                                              (x, phi),
                                              FStar_Pervasives_Native.None)
                                               ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)] in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi in
                                               let uu____12622 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12622
                                           | uu____12625 -> t_base in
                                         let uu____12642 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu____12642 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____12656 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu____12656, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu____12663 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu____12663 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu____12698 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu____12698 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu____12733 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu____12733
                                                         with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu____12757 = combine t11 t21 wl2 in
                              (match uu____12757 with
                               | (t12, ps, wl3) ->
                                   ((let uu____12790 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu____12790
                                     then
                                       let uu____12791 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____12791
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu____12830 ts1 =
               match uu____12830 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12893 = pairwise out t wl2 in
                        (match uu____12893 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2)) in
             let uu____12929 =
               let uu____12940 = FStar_List.hd ts in (uu____12940, [], wl1) in
             let uu____12949 = FStar_List.tl ts in
             aux uu____12929 uu____12949 in
           let uu____12956 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu____12956 with
           | (this_flex, this_rigid) ->
               let uu____12980 =
                 let uu____12981 = FStar_Syntax_Subst.compress this_rigid in
                 uu____12981.FStar_Syntax_Syntax.n in
               (match uu____12980 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu____13006 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu____13006
                    then
                      let uu____13007 = destruct_flex_t this_flex wl in
                      (match uu____13007 with
                       | (flex, wl1) ->
                           let uu____13014 = quasi_pattern env flex in
                           (match uu____13014 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu____13032 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____13032
                                  then
                                    let uu____13033 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13033
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13036 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2048_13039 = tp in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2048_13039.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2048_13039.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2048_13039.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2048_13039.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2048_13039.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2048_13039.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2048_13039.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2048_13039.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2048_13039.FStar_TypeChecker_Common.rank)
                                }))] wl in
                       solve env uu____13036)
                | uu____13040 ->
                    ((let uu____13042 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____13042
                      then
                        let uu____13043 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13043
                      else ());
                     (let uu____13045 =
                        FStar_Syntax_Util.head_and_args this_flex in
                      match uu____13045 with
                      | (u, _args) ->
                          let uu____13088 =
                            let uu____13089 = FStar_Syntax_Subst.compress u in
                            uu____13089.FStar_Syntax_Syntax.n in
                          (match uu____13088 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu____13116 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu____13116 with
                                 | (u', uu____13134) ->
                                     let uu____13159 =
                                       let uu____13160 = whnf env u' in
                                       uu____13160.FStar_Syntax_Syntax.n in
                                     (match uu____13159 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13181 -> false) in
                               let uu____13182 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13205 ->
                                         match uu___23_13205 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1 in
                                             (match tp2.FStar_TypeChecker_Common.rank
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  rank' when rank1 = rank' ->
                                                  if flip
                                                  then
                                                    equiv
                                                      tp2.FStar_TypeChecker_Common.lhs
                                                  else
                                                    equiv
                                                      tp2.FStar_TypeChecker_Common.rhs
                                              | uu____13214 -> false)
                                         | uu____13217 -> false)) in
                               (match uu____13182 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu____13231 = whnf env this_rigid in
                                      let uu____13232 =
                                        FStar_List.collect
                                          (fun uu___24_13238 ->
                                             match uu___24_13238 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13244 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu____13244]
                                             | uu____13246 -> [])
                                          bounds_probs in
                                      uu____13231 :: uu____13232 in
                                    let uu____13247 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu____13247 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu____13278 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu____13293 =
                                               let uu____13294 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu____13294.FStar_Syntax_Syntax.n in
                                             match uu____13293 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13306 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13306)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13315 -> bound in
                                           let uu____13316 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu____13316) in
                                         (match uu____13278 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13345 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu____13345
                                                then
                                                  let wl'1 =
                                                    let uu___2108_13347 = wl1 in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2108_13347.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2108_13347.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2108_13347.ctr);
                                                      defer_ok =
                                                        (uu___2108_13347.defer_ok);
                                                      smt_ok =
                                                        (uu___2108_13347.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2108_13347.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2108_13347.tcenv);
                                                      wl_implicits =
                                                        (uu___2108_13347.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2108_13347.repr_subcomp_allowed)
                                                    } in
                                                  let uu____13348 =
                                                    wl_to_string wl'1 in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13348
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____13351 =
                                                  solve_t env eq_prob
                                                    (let uu___2113_13353 =
                                                       wl' in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2113_13353.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2113_13353.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2113_13353.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2113_13353.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2113_13353.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2113_13353.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2113_13353.repr_subcomp_allowed)
                                                     }) in
                                                match uu____13351 with
                                                | Success
                                                    (uu____13354,
                                                     defer_to_tac, imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2120_13358 =
                                                        wl' in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2120_13358.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2120_13358.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2120_13358.ctr);
                                                        defer_ok =
                                                          (uu___2120_13358.defer_ok);
                                                        smt_ok =
                                                          (uu___2120_13358.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2120_13358.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2120_13358.tcenv);
                                                        wl_implicits =
                                                          (uu___2120_13358.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2120_13358.repr_subcomp_allowed)
                                                      } in
                                                    let wl3 =
                                                      extend_wl wl2
                                                        defer_to_tac imps in
                                                    let g =
                                                      FStar_List.fold_left
                                                        (fun g ->
                                                           fun p ->
                                                             FStar_Syntax_Util.mk_conj
                                                               g (p_guard p))
                                                        eq_prob.FStar_TypeChecker_Common.logical_guard
                                                        sub_probs in
                                                    let wl4 =
                                                      solve_prob' false
                                                        (FStar_TypeChecker_Common.TProb
                                                           tp)
                                                        (FStar_Pervasives_Native.Some
                                                           g) [] wl3 in
                                                    let uu____13374 =
                                                      FStar_List.fold_left
                                                        (fun wl5 ->
                                                           fun p ->
                                                             solve_prob' true
                                                               p
                                                               FStar_Pervasives_Native.None
                                                               [] wl5) wl4
                                                        bounds_probs in
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     solve env wl4)
                                                | Failed (p, msg) ->
                                                    ((let uu____13385 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu____13385
                                                      then
                                                        let uu____13386 =
                                                          let uu____13387 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_All.pipe_right
                                                            uu____13387
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13386
                                                      else ());
                                                     (let uu____13393 =
                                                        let uu____13408 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu____13408) in
                                                      match uu____13393 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu____13430)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13456 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13456
                                                            with
                                                            | (eq_prob1, wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join3"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let wl3 =
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    (FStar_Pervasives_Native.Some
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)))
                                                                    [] wl2 in
                                                                  let uu____13473
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13473))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13498 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13498
                                                            with
                                                            | (eq_prob1, wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join4"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let phi1 =
                                                                    guard_on_element
                                                                    wl2 tp x
                                                                    phi in
                                                                  let wl3 =
                                                                    let uu____13516
                                                                    =
                                                                    let uu____13521
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13521 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13516
                                                                    [] wl2 in
                                                                  let uu____13526
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13526))))
                                                      | uu____13527 ->
                                                          let uu____13542 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env
                                                            uu____13542 p)))))))
                           | uu____13545 when flip ->
                               let uu____13546 =
                                 let uu____13547 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13548 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13547 uu____13548 in
                               failwith uu____13546
                           | uu____13549 ->
                               let uu____13550 =
                                 let uu____13551 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13552 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13551 uu____13552 in
                               failwith uu____13550)))))
and (imitate_arrow :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        flex_t ->
          FStar_Syntax_Syntax.binders ->
            FStar_Syntax_Syntax.term ->
              FStar_TypeChecker_Common.rel ->
                FStar_Syntax_Syntax.term -> solution)
  =
  fun orig ->
    fun env ->
      fun wl ->
        fun lhs ->
          fun bs_lhs ->
            fun t_res_lhs ->
              fun rel ->
                fun arrow ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____13586 ->
                         match uu____13586 with
                         | (x, i) ->
                             let uu____13605 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             (uu____13605, i)) bs_lhs in
                  let uu____13608 = lhs in
                  match uu____13608 with
                  | Flex (uu____13609, u_lhs, uu____13611) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____13708 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____13718 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu____13718, univ) in
                          match uu____13708 with
                          | (k, univ) ->
                              let uu____13725 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2 in
                              (match uu____13725 with
                               | (uu____13742, u, wl3) ->
                                   let uu____13745 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu____13745, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____13771 =
                              let uu____13784 =
                                let uu____13795 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu____13795 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_List.fold_right
                                (fun uu____13846 ->
                                   fun uu____13847 ->
                                     match (uu____13846, uu____13847) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu____13948 =
                                           let uu____13955 =
                                             let uu____13958 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13958 in
                                           copy_uvar u_lhs [] uu____13955 wl2 in
                                         (match uu____13948 with
                                          | (uu____13987, t_a, wl3) ->
                                              let uu____13990 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu____13990 with
                                               | (uu____14009, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____13784
                                ([], wl1) in
                            (match uu____13771 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_14078 ->
                                        match uu___25_14078 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____14079 -> false
                                        | uu____14082 -> true) flags in
                                 let ct' =
                                   let uu___2239_14084 = ct in
                                   let uu____14085 =
                                     let uu____14088 = FStar_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu____14088 in
                                   let uu____14103 = FStar_List.tl out_args in
                                   let uu____14120 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2239_14084.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2239_14084.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14085;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14103;
                                     FStar_Syntax_Syntax.flags = uu____14120
                                   } in
                                 ((let uu___2242_14124 = c in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2242_14124.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2242_14124.FStar_Syntax_Syntax.vars)
                                   }), wl2)) in
                      let uu____14127 =
                        FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu____14127 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14165 =
                                   imitate_comp bs bs_terms c wl1 in
                                 (match uu____14165 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu____14176 =
                                          let uu____14181 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____14181) in
                                        TERM uu____14176 in
                                      let uu____14182 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu____14182 with
                                       | (sub_prob, wl3) ->
                                           let uu____14195 =
                                             let uu____14196 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu____14196 in
                                           solve env uu____14195))
                             | (x, imp)::formals2 ->
                                 let uu____14218 =
                                   let uu____14225 =
                                     let uu____14228 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____14228
                                       FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14225 wl1 in
                                 (match uu____14218 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu____14249 =
                                          let uu____14252 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some
                                            uu____14252 in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14249 u_x in
                                      let uu____14253 =
                                        let uu____14256 =
                                          let uu____14259 =
                                            let uu____14260 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y in
                                            (uu____14260, imp) in
                                          [uu____14259] in
                                        FStar_List.append bs_terms
                                          uu____14256 in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14253 formals2 wl2) in
                           let uu____14287 = occurs_check u_lhs arrow in
                           (match uu____14287 with
                            | (uu____14298, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14309 =
                                    mklstr
                                      (fun uu____14314 ->
                                         let uu____14315 =
                                           FStar_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14315) in
                                  giveup_or_defer env orig wl uu____14309
                                else aux [] [] formals wl))
and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (worklist ->
               FStar_Syntax_Syntax.binders ->
                 FStar_TypeChecker_Env.env ->
                   FStar_Syntax_Syntax.subst_elt Prims.list ->
                     (FStar_TypeChecker_Common.prob * worklist))
              -> solution)
  =
  fun env ->
    fun bs1 ->
      fun bs2 ->
        fun orig ->
          fun wl ->
            fun rhs ->
              (let uu____14344 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____14344
               then
                 let uu____14345 =
                   FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu____14346 =
                   FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14345 (rel_to_string (p_rel orig)) uu____14346
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu____14471 = rhs wl1 scope env1 subst in
                     (match uu____14471 with
                      | (rhs_prob, wl2) ->
                          ((let uu____14493 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu____14493
                            then
                              let uu____14494 = prob_to_string env1 rhs_prob in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14494
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1, imp)::xs1, (hd2, imp')::ys1) when
                     let uu____14567 = FStar_Syntax_Util.eq_aqual imp imp' in
                     uu____14567 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2312_14569 = hd1 in
                       let uu____14570 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2312_14569.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2312_14569.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14570
                       } in
                     let hd21 =
                       let uu___2315_14574 = hd2 in
                       let uu____14575 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2315_14574.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2315_14574.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14575
                       } in
                     let uu____14578 =
                       let uu____14583 =
                         FStar_All.pipe_left invert_rel (p_rel orig) in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____14583
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter" in
                     (match uu____14578 with
                      | (prob, wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                          let subst1 =
                            let uu____14604 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____14604 in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                          let uu____14608 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1 in
                          (match uu____14608 with
                           | (env3, FStar_Util.Inl (sub_probs, phi), wl3) ->
                               let phi1 =
                                 let uu____14676 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____14676 in
                               ((let uu____14694 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14694
                                 then
                                   let uu____14695 =
                                     FStar_Syntax_Print.term_to_string phi1 in
                                   let uu____14696 =
                                     FStar_Syntax_Print.bv_to_string hd12 in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____14695
                                     uu____14696
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____14725 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1) in
               let uu____14758 = aux wl [] env [] bs1 bs2 in
               match uu____14758 with
               | (env1, FStar_Util.Inr msg, wl1) -> giveup_lit env1 msg orig
               | (env1, FStar_Util.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu____14811 = attempt sub_probs wl2 in
                   solve env1 uu____14811)
and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist -> (FStar_TypeChecker_Common.prob * lstring) -> solution)
          -> solution)
  =
  fun env ->
    fun wl ->
      fun try_solve ->
        fun else_solve ->
          let wl' =
            let uu___2353_14831 = wl in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2353_14831.wl_deferred_to_tac);
              ctr = (uu___2353_14831.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2353_14831.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2353_14831.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu____14839 = try_solve env wl' in
          match uu____14839 with
          | Success (uu____14840, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____14852 = compress_tprob wl.tcenv problem in
         solve_t' env uu____14852 wl)
and (solve_t_flex_rigid_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist -> flex_t -> FStar_Syntax_Syntax.term -> solution)
  =
  fun env ->
    fun orig ->
      fun wl ->
        fun lhs ->
          fun rhs ->
            (let uu____14859 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Rel") in
             if uu____14859
             then FStar_Util.print_string "solve_t_flex_rigid_eq\n"
             else ());
            (let uu____14861 = should_defer_flex_to_user_tac env wl lhs in
             if uu____14861
             then defer_to_user_tac env orig (flex_reason lhs) wl
             else
               (let binders_as_bv_set bs =
                  let uu____14871 =
                    FStar_List.map FStar_Pervasives_Native.fst bs in
                  FStar_Util.as_set uu____14871 FStar_Syntax_Syntax.order_bv in
                let mk_solution env1 lhs1 bs rhs1 =
                  let uu____14905 = lhs1 in
                  match uu____14905 with
                  | Flex (uu____14908, ctx_u, uu____14910) ->
                      let sol =
                        match bs with
                        | [] -> rhs1
                        | uu____14918 ->
                            let uu____14919 = sn_binders env1 bs in
                            u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                              uu____14919 rhs1 in
                      [TERM (ctx_u, sol)] in
                let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                  (let uu____14967 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu____14967
                   then FStar_Util.print_string "try_quasi_pattern\n"
                   else ());
                  (let uu____14969 = quasi_pattern env1 lhs1 in
                   match uu____14969 with
                   | FStar_Pervasives_Native.None ->
                       ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                   | FStar_Pervasives_Native.Some (bs, uu____14999) ->
                       let uu____15004 = lhs1 in
                       (match uu____15004 with
                        | Flex (t_lhs, ctx_u, args) ->
                            let uu____15018 = occurs_check ctx_u rhs1 in
                            (match uu____15018 with
                             | (uvars, occurs_ok, msg) ->
                                 if Prims.op_Negation occurs_ok
                                 then
                                   let uu____15060 =
                                     let uu____15067 =
                                       let uu____15068 = FStar_Option.get msg in
                                       Prims.op_Hat
                                         "quasi-pattern, occurs-check failed: "
                                         uu____15068 in
                                     FStar_Util.Inl uu____15067 in
                                   (uu____15060, wl1)
                                 else
                                   (let fvs_lhs =
                                      binders_as_bv_set
                                        (FStar_List.append
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                           bs) in
                                    let fvs_rhs =
                                      FStar_Syntax_Free.names rhs1 in
                                    let uu____15090 =
                                      let uu____15091 =
                                        FStar_Util.set_is_subset_of fvs_rhs
                                          fvs_lhs in
                                      Prims.op_Negation uu____15091 in
                                    if uu____15090
                                    then
                                      ((FStar_Util.Inl
                                          "quasi-pattern, free names on the RHS are not included in the LHS"),
                                        wl1)
                                    else
                                      (let uu____15111 =
                                         let uu____15118 =
                                           mk_solution env1 lhs1 bs rhs1 in
                                         FStar_Util.Inr uu____15118 in
                                       let uu____15123 =
                                         restrict_all_uvars env1 ctx_u []
                                           uvars wl1 in
                                       (uu____15111, uu____15123)))))) in
                let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                  let uu____15172 = FStar_Syntax_Util.head_and_args rhs1 in
                  match uu____15172 with
                  | (rhs_hd, args) ->
                      let uu____15215 = FStar_Util.prefix args in
                      (match uu____15215 with
                       | (args_rhs, last_arg_rhs) ->
                           let rhs' =
                             FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                               rhs1.FStar_Syntax_Syntax.pos in
                           let uu____15285 = lhs1 in
                           (match uu____15285 with
                            | Flex (t_lhs, u_lhs, _lhs_args) ->
                                let uu____15289 =
                                  let uu____15300 =
                                    let uu____15307 =
                                      let uu____15310 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_left
                                        FStar_Pervasives_Native.fst
                                        uu____15310 in
                                    copy_uvar u_lhs [] uu____15307 wl1 in
                                  match uu____15300 with
                                  | (uu____15337, t_last_arg, wl2) ->
                                      let uu____15340 =
                                        let uu____15347 =
                                          let uu____15348 =
                                            let uu____15357 =
                                              FStar_Syntax_Syntax.null_binder
                                                t_last_arg in
                                            [uu____15357] in
                                          FStar_List.append bs_lhs
                                            uu____15348 in
                                        copy_uvar u_lhs uu____15347 t_res_lhs
                                          wl2 in
                                      (match uu____15340 with
                                       | (uu____15392, lhs', wl3) ->
                                           let uu____15395 =
                                             copy_uvar u_lhs bs_lhs
                                               t_last_arg wl3 in
                                           (match uu____15395 with
                                            | (uu____15412, lhs'_last_arg,
                                               wl4) ->
                                                (lhs', lhs'_last_arg, wl4))) in
                                (match uu____15289 with
                                 | (lhs', lhs'_last_arg, wl2) ->
                                     let sol =
                                       let uu____15433 =
                                         let uu____15434 =
                                           let uu____15439 =
                                             let uu____15440 =
                                               let uu____15443 =
                                                 let uu____15444 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lhs'_last_arg in
                                                 [uu____15444] in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 lhs' uu____15443
                                                 t_lhs.FStar_Syntax_Syntax.pos in
                                             FStar_Syntax_Util.abs bs_lhs
                                               uu____15440
                                               (FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Util.residual_tot
                                                     t_res_lhs)) in
                                           (u_lhs, uu____15439) in
                                         TERM uu____15434 in
                                       [uu____15433] in
                                     let uu____15469 =
                                       let uu____15476 =
                                         mk_t_problem wl2 [] orig1 lhs'
                                           FStar_TypeChecker_Common.EQ rhs'
                                           FStar_Pervasives_Native.None
                                           "first-order lhs" in
                                       match uu____15476 with
                                       | (p1, wl3) ->
                                           let uu____15495 =
                                             mk_t_problem wl3 [] orig1
                                               lhs'_last_arg
                                               FStar_TypeChecker_Common.EQ
                                               (FStar_Pervasives_Native.fst
                                                  last_arg_rhs)
                                               FStar_Pervasives_Native.None
                                               "first-order rhs" in
                                           (match uu____15495 with
                                            | (p2, wl4) -> ([p1; p2], wl4)) in
                                     (match uu____15469 with
                                      | (sub_probs, wl3) ->
                                          let uu____15526 =
                                            let uu____15527 =
                                              solve_prob orig1
                                                FStar_Pervasives_Native.None
                                                sol wl3 in
                                            attempt sub_probs uu____15527 in
                                          solve env1 uu____15526)))) in
                let first_order orig1 env1 wl1 lhs1 rhs1 =
                  (let uu____15555 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu____15555
                   then FStar_Util.print_string "first_order\n"
                   else ());
                  (let is_app rhs2 =
                     let uu____15563 = FStar_Syntax_Util.head_and_args rhs2 in
                     match uu____15563 with
                     | (uu____15580, args) ->
                         (match args with | [] -> false | uu____15614 -> true) in
                   let is_arrow rhs2 =
                     let uu____15631 =
                       let uu____15632 = FStar_Syntax_Subst.compress rhs2 in
                       uu____15632.FStar_Syntax_Syntax.n in
                     match uu____15631 with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15635 -> true
                     | uu____15650 -> false in
                   let uu____15651 = quasi_pattern env1 lhs1 in
                   match uu____15651 with
                   | FStar_Pervasives_Native.None ->
                       let msg =
                         mklstr
                           (fun uu____15669 ->
                              let uu____15670 = prob_to_string env1 orig1 in
                              FStar_Util.format1
                                "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                                uu____15670) in
                       giveup_or_defer env1 orig1 wl1 msg
                   | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                       let uu____15677 = is_app rhs1 in
                       if uu____15677
                       then
                         imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                           rhs1
                       else
                         (let uu____15679 = is_arrow rhs1 in
                          if uu____15679
                          then
                            imitate_arrow orig1 env1 wl1 lhs1 bs_lhs
                              t_res_lhs FStar_TypeChecker_Common.EQ rhs1
                          else
                            (let msg =
                               mklstr
                                 (fun uu____15688 ->
                                    let uu____15689 =
                                      prob_to_string env1 orig1 in
                                    FStar_Util.format1
                                      "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                      uu____15689) in
                             giveup_or_defer env1 orig1 wl1 msg))) in
                match p_rel orig with
                | FStar_TypeChecker_Common.SUB ->
                    if wl.defer_ok
                    then
                      let uu____15690 =
                        FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl uu____15690
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.SUBINV ->
                    if wl.defer_ok
                    then
                      let uu____15692 =
                        FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl uu____15692
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.EQ ->
                    let uu____15694 = lhs in
                    (match uu____15694 with
                     | Flex (_t1, ctx_uv, args_lhs) ->
                         let uu____15698 =
                           pat_vars env
                             ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                             args_lhs in
                         (match uu____15698 with
                          | FStar_Pervasives_Native.Some lhs_binders ->
                              ((let uu____15705 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel") in
                                if uu____15705
                                then
                                  FStar_Util.print_string "it's a pattern\n"
                                else ());
                               (let rhs1 = sn env rhs in
                                let names_to_string1 fvs =
                                  let uu____15718 =
                                    let uu____15721 =
                                      FStar_Util.set_elements fvs in
                                    FStar_List.map
                                      FStar_Syntax_Print.bv_to_string
                                      uu____15721 in
                                  FStar_All.pipe_right uu____15718
                                    (FStar_String.concat ", ") in
                                let fvs1 =
                                  binders_as_bv_set
                                    (FStar_List.append
                                       ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                       lhs_binders) in
                                let fvs2 = FStar_Syntax_Free.names rhs1 in
                                let uu____15738 = occurs_check ctx_uv rhs1 in
                                match uu____15738 with
                                | (uvars, occurs_ok, msg) ->
                                    if Prims.op_Negation occurs_ok
                                    then
                                      let uu____15760 =
                                        let uu____15761 =
                                          let uu____15762 =
                                            FStar_Option.get msg in
                                          Prims.op_Hat
                                            "occurs-check failed: "
                                            uu____15762 in
                                        FStar_All.pipe_left FStar_Thunk.mkv
                                          uu____15761 in
                                      giveup_or_defer env orig wl uu____15760
                                    else
                                      (let uu____15764 =
                                         FStar_Util.set_is_subset_of fvs2
                                           fvs1 in
                                       if uu____15764
                                       then
                                         let sol =
                                           mk_solution env lhs lhs_binders
                                             rhs1 in
                                         let wl1 =
                                           restrict_all_uvars env ctx_uv
                                             lhs_binders uvars wl in
                                         let uu____15769 =
                                           solve_prob orig
                                             FStar_Pervasives_Native.None sol
                                             wl1 in
                                         solve env uu____15769
                                       else
                                         if wl.defer_ok
                                         then
                                           (let msg1 =
                                              mklstr
                                                (fun uu____15782 ->
                                                   let uu____15783 =
                                                     names_to_string1 fvs2 in
                                                   let uu____15784 =
                                                     names_to_string1 fvs1 in
                                                   let uu____15785 =
                                                     FStar_Syntax_Print.binders_to_string
                                                       ", "
                                                       (FStar_List.append
                                                          ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                          lhs_binders) in
                                                   FStar_Util.format3
                                                     "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                     uu____15783 uu____15784
                                                     uu____15785) in
                                            giveup_or_defer env orig wl msg1)
                                         else
                                           first_order orig env wl lhs rhs1)))
                          | uu____15793 ->
                              if wl.defer_ok
                              then
                                let uu____15796 =
                                  FStar_Thunk.mkv "Not a pattern" in
                                giveup_or_defer env orig wl uu____15796
                              else
                                (let uu____15798 =
                                   try_quasi_pattern orig env wl lhs rhs in
                                 match uu____15798 with
                                 | (FStar_Util.Inr sol, wl1) ->
                                     let uu____15821 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None sol wl1 in
                                     solve env uu____15821
                                 | (FStar_Util.Inl msg, uu____15823) ->
                                     first_order orig env wl lhs rhs)))))
and (solve_t_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> flex_t -> flex_t -> solution)
  =
  fun env ->
    fun orig ->
      fun wl ->
        fun lhs ->
          fun rhs ->
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB ->
                if wl.defer_ok
                then
                  let uu____15837 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15837
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok
                then
                  let uu____15839 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15839
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu____15841 =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu____15841
                then
                  defer_to_user_tac env orig
                    (Prims.op_Hat (flex_reason lhs)
                       (Prims.op_Hat ", " (flex_reason rhs))) wl
                else
                  if
                    wl.defer_ok &&
                      ((Prims.op_Negation (is_flex_pat lhs)) ||
                         (Prims.op_Negation (is_flex_pat rhs)))
                  then
                    (let uu____15843 =
                       FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer env orig wl uu____15843)
                  else
                    (let uu____15845 =
                       let uu____15862 = quasi_pattern env lhs in
                       let uu____15869 = quasi_pattern env rhs in
                       (uu____15862, uu____15869) in
                     match uu____15845 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs, t_res_lhs),
                        FStar_Pervasives_Native.Some
                        (binders_rhs, t_res_rhs)) ->
                         let uu____15912 = lhs in
                         (match uu____15912 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____15913;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____15915;_},
                               u_lhs, uu____15917)
                              ->
                              let uu____15920 = rhs in
                              (match uu____15920 with
                               | Flex (uu____15921, u_rhs, uu____15923) ->
                                   let uu____15924 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs) in
                                   if uu____15924
                                   then
                                     let uu____15929 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl in
                                     solve env uu____15929
                                   else
                                     (let uu____15931 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                      match uu____15931 with
                                      | (ctx_w, (ctx_l, ctx_r)) ->
                                          let gamma_w =
                                            gamma_until
                                              u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                              ctx_w in
                                          let zs =
                                            intersect_binders gamma_w
                                              (FStar_List.append ctx_l
                                                 binders_lhs)
                                              (FStar_List.append ctx_r
                                                 binders_rhs) in
                                          let uu____15963 =
                                            let uu____15970 =
                                              let uu____15973 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs in
                                              FStar_Syntax_Util.arrow zs
                                                uu____15973 in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____15970
                                              (if
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    =
                                                    FStar_Syntax_Syntax.Allow_untyped)
                                                   &&
                                                   (u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                      =
                                                      FStar_Syntax_Syntax.Allow_untyped)
                                               then
                                                 FStar_Syntax_Syntax.Allow_untyped
                                               else
                                                 FStar_Syntax_Syntax.Strict)
                                              FStar_Pervasives_Native.None in
                                          (match uu____15963 with
                                           | (uu____15977, w, wl1) ->
                                               let w_app =
                                                 let uu____15981 =
                                                   FStar_List.map
                                                     (fun uu____15992 ->
                                                        match uu____15992
                                                        with
                                                        | (z, uu____16000) ->
                                                            let uu____16005 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16005) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____15981
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____16007 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16007
                                                 then
                                                   let uu____16008 =
                                                     let uu____16011 =
                                                       flex_t_to_string lhs in
                                                     let uu____16012 =
                                                       let uu____16015 =
                                                         flex_t_to_string rhs in
                                                       let uu____16016 =
                                                         let uu____16019 =
                                                           term_to_string w in
                                                         let uu____16020 =
                                                           let uu____16023 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____16030 =
                                                             let uu____16033
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____16040
                                                               =
                                                               let uu____16043
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____16043] in
                                                             uu____16033 ::
                                                               uu____16040 in
                                                           uu____16023 ::
                                                             uu____16030 in
                                                         uu____16019 ::
                                                           uu____16020 in
                                                       uu____16015 ::
                                                         uu____16016 in
                                                     uu____16011 ::
                                                       uu____16012 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____16008
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____16049 =
                                                       let uu____16054 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____16054) in
                                                     TERM uu____16049 in
                                                   let uu____16055 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____16055
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____16060 =
                                                          let uu____16065 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____16065) in
                                                        TERM uu____16060 in
                                                      [s1; s2]) in
                                                 let uu____16066 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____16066))))))
                     | uu____16067 ->
                         let uu____16084 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____16084)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____16133 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____16133
            then
              let uu____16134 = FStar_Syntax_Print.term_to_string t1 in
              let uu____16135 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____16136 = FStar_Syntax_Print.term_to_string t2 in
              let uu____16137 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16134 uu____16135 uu____16136 uu____16137
            else ());
           (let uu____16140 = FStar_Syntax_Util.head_and_args t1 in
            match uu____16140 with
            | (head1, args1) ->
                let uu____16183 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____16183 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16248 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____16248 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____16252 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____16252) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16270 =
                         mklstr
                           (fun uu____16281 ->
                              let uu____16282 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____16283 = args_to_string args1 in
                              let uu____16286 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____16287 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____16282 uu____16283 uu____16286
                                uu____16287) in
                       giveup env1 uu____16270 orig
                     else
                       (let uu____16291 =
                          (nargs = Prims.int_zero) ||
                            (let uu____16293 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____16293 = FStar_Syntax_Util.Equal) in
                        if uu____16291
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2634_16295 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2634_16295.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2634_16295.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2634_16295.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2634_16295.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2634_16295.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2634_16295.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2634_16295.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2634_16295.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____16302 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____16302
                                    else solve env1 wl2))
                        else
                          (let uu____16305 = base_and_refinement env1 t1 in
                           match uu____16305 with
                           | (base1, refinement1) ->
                               let uu____16330 = base_and_refinement env1 t2 in
                               (match uu____16330 with
                                | (base2, refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None) ->
                                         let mk_sub_probs wl2 =
                                           let argp =
                                             if need_unif
                                             then
                                               FStar_List.zip
                                                 ((head1,
                                                    FStar_Pervasives_Native.None)
                                                 :: args1)
                                                 ((head2,
                                                    FStar_Pervasives_Native.None)
                                                 :: args2)
                                             else FStar_List.zip args1 args2 in
                                           let uu____16493 =
                                             FStar_List.fold_right
                                               (fun uu____16533 ->
                                                  fun uu____16534 ->
                                                    match (uu____16533,
                                                            uu____16534)
                                                    with
                                                    | (((a1, uu____16586),
                                                        (a2, uu____16588)),
                                                       (probs, wl3)) ->
                                                        let uu____16637 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____16637
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____16493 with
                                           | (subprobs, wl3) ->
                                               ((let uu____16679 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16679
                                                 then
                                                   let uu____16680 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____16680
                                                 else ());
                                                (let uu____16683 =
                                                   FStar_Options.defensive () in
                                                 if uu____16683
                                                 then
                                                   FStar_List.iter
                                                     (def_check_prob
                                                        "solve_t' subprobs")
                                                     subprobs
                                                 else ());
                                                (subprobs, wl3)) in
                                         let solve_sub_probs env2 wl2 =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  if Prims.op_Negation ok
                                                  then solve env2 wl3
                                                  else
                                                    (let uu____16703 =
                                                       mk_sub_probs wl3 in
                                                     match uu____16703 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____16719 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____16719 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____16727 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____16727)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____16751 =
                                                    mk_sub_probs wl3 in
                                                  match uu____16751 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____16767 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____16767 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____16775 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____16775) in
                                         let unfold_and_retry d env2 wl2
                                           uu____16802 =
                                           match uu____16802 with
                                           | (prob, reason) ->
                                               ((let uu____16816 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16816
                                                 then
                                                   let uu____16817 =
                                                     prob_to_string env2 orig in
                                                   let uu____16818 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____16817 uu____16818
                                                 else ());
                                                (let uu____16820 =
                                                   let uu____16829 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____16832 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____16829, uu____16832) in
                                                 match uu____16820 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____16845 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____16845 with
                                                      | (head1', uu____16863)
                                                          ->
                                                          let uu____16888 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____16888
                                                           with
                                                           | (head2',
                                                              uu____16906) ->
                                                               let uu____16931
                                                                 =
                                                                 let uu____16936
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____16937
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____16936,
                                                                   uu____16937) in
                                                               (match uu____16931
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu____16939
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____16939
                                                                    then
                                                                    let uu____16940
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____16941
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____16942
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____16943
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____16940
                                                                    uu____16941
                                                                    uu____16942
                                                                    uu____16943
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____16945
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2722_16953
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2722_16953.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2722_16953.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2722_16953.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2722_16953.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2722_16953.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2722_16953.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2722_16953.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2722_16953.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
                                                                    let uu____16955
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____16955
                                                                    then
                                                                    let uu____16956
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____16956
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____16958 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____16970 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____16970 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____16977 =
                                             let uu____16978 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____16978.FStar_Syntax_Syntax.n in
                                           match uu____16977 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____16982 -> false in
                                         (match d with
                                          | FStar_Pervasives_Native.Some d1
                                              when
                                              wl1.smt_ok &&
                                                (Prims.op_Negation
                                                   treat_as_injective)
                                              ->
                                              try_solve_without_smt_or_else
                                                env1 wl1
                                                solve_sub_probs_no_smt
                                                (unfold_and_retry d1)
                                          | uu____16984 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____16987 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2742_17023 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2742_17023.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2742_17023.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2742_17023.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2742_17023.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2742_17023.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2742_17023.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2742_17023.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2742_17023.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17098 = destruct_flex_t scrutinee wl1 in
             match uu____17098 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____17109 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____17109 with
                  | (xs, pat_term, uu____17124, uu____17125) ->
                      let uu____17130 =
                        FStar_List.fold_left
                          (fun uu____17153 ->
                             fun x ->
                               match uu____17153 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____17174 = copy_uvar uv [] t_x wl3 in
                                   (match uu____17174 with
                                    | (uu____17193, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____17130 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____17214 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____17214 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2783_17230 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2783_17230.wl_deferred_to_tac);
                                    ctr = (uu___2783_17230.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2783_17230.umax_heuristic_ok);
                                    tcenv = (uu___2783_17230.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2783_17230.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____17238 = solve env1 wl' in
                                (match uu____17238 with
                                 | Success (uu____17241, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2792_17245 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2792_17245.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2792_17245.wl_deferred_to_tac);
                                         ctr = (uu___2792_17245.ctr);
                                         defer_ok =
                                           (uu___2792_17245.defer_ok);
                                         smt_ok = (uu___2792_17245.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2792_17245.umax_heuristic_ok);
                                         tcenv = (uu___2792_17245.tcenv);
                                         wl_implicits =
                                           (uu___2792_17245.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2792_17245.repr_subcomp_allowed)
                                       } in
                                     let uu____17246 = solve env1 wl'1 in
                                     (match uu____17246 with
                                      | Success
                                          (uu____17249, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____17253 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____17253))
                                      | Failed uu____17258 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17264 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____17285 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____17285
                 then
                   let uu____17286 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____17287 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17286 uu____17287
                 else ());
                (let uu____17289 =
                   let uu____17310 =
                     let uu____17319 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____17319) in
                   let uu____17326 =
                     let uu____17335 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____17335) in
                   (uu____17310, uu____17326) in
                 match uu____17289 with
                 | ((uu____17364,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____17367;
                       FStar_Syntax_Syntax.vars = uu____17368;_}),
                    (s, t)) ->
                     let uu____17439 =
                       let uu____17440 = is_flex scrutinee in
                       Prims.op_Negation uu____17440 in
                     if uu____17439
                     then
                       ((let uu____17448 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____17448
                         then
                           let uu____17449 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17449
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17461 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17461
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17467 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17467
                           then
                             let uu____17468 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____17469 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17468 uu____17469
                           else ());
                          (let pat_discriminates uu___26_17490 =
                             match uu___26_17490 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17505;
                                  FStar_Syntax_Syntax.p = uu____17506;_},
                                FStar_Pervasives_Native.None, uu____17507) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17520;
                                  FStar_Syntax_Syntax.p = uu____17521;_},
                                FStar_Pervasives_Native.None, uu____17522) ->
                                 true
                             | uu____17547 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____17647 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____17647 with
                                       | (uu____17648, uu____17649, t') ->
                                           let uu____17667 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____17667 with
                                            | (FullMatch, uu____17678) ->
                                                true
                                            | (HeadMatch uu____17691,
                                               uu____17692) -> true
                                            | uu____17705 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____17738 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____17738
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17743 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____17743 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____17831, uu____17832)
                                       -> branches1
                                   | uu____17977 -> branches in
                                 let uu____18032 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____18041 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____18041 with
                                        | (p, uu____18045, uu____18046) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____18073 ->
                                      FStar_Util.Inr uu____18073) uu____18032))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18103 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____18103 with
                                | (p, uu____18111, e) ->
                                    ((let uu____18130 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____18130
                                      then
                                        let uu____18131 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____18132 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18131 uu____18132
                                      else ());
                                     (let uu____18134 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____18147 ->
                                           FStar_Util.Inr uu____18147)
                                        uu____18134)))))
                 | ((s, t),
                    (uu____18150,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____18153;
                       FStar_Syntax_Syntax.vars = uu____18154;_}))
                     ->
                     let uu____18223 =
                       let uu____18224 = is_flex scrutinee in
                       Prims.op_Negation uu____18224 in
                     if uu____18223
                     then
                       ((let uu____18232 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____18232
                         then
                           let uu____18233 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18233
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18245 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18245
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18251 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18251
                           then
                             let uu____18252 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____18253 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18252 uu____18253
                           else ());
                          (let pat_discriminates uu___26_18274 =
                             match uu___26_18274 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18289;
                                  FStar_Syntax_Syntax.p = uu____18290;_},
                                FStar_Pervasives_Native.None, uu____18291) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18304;
                                  FStar_Syntax_Syntax.p = uu____18305;_},
                                FStar_Pervasives_Native.None, uu____18306) ->
                                 true
                             | uu____18331 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____18431 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____18431 with
                                       | (uu____18432, uu____18433, t') ->
                                           let uu____18451 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____18451 with
                                            | (FullMatch, uu____18462) ->
                                                true
                                            | (HeadMatch uu____18475,
                                               uu____18476) -> true
                                            | uu____18489 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____18522 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____18522
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18527 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____18527 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____18615, uu____18616)
                                       -> branches1
                                   | uu____18761 -> branches in
                                 let uu____18816 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____18825 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____18825 with
                                        | (p, uu____18829, uu____18830) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____18857 ->
                                      FStar_Util.Inr uu____18857) uu____18816))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18887 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____18887 with
                                | (p, uu____18895, e) ->
                                    ((let uu____18914 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____18914
                                      then
                                        let uu____18915 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____18916 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18915 uu____18916
                                      else ());
                                     (let uu____18918 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____18931 ->
                                           FStar_Util.Inr uu____18931)
                                        uu____18918)))))
                 | uu____18932 ->
                     ((let uu____18954 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____18954
                       then
                         let uu____18955 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____18956 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____18955 uu____18956
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____18998 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____18998
            then
              let uu____18999 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____19000 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____19001 = FStar_Syntax_Print.term_to_string t1 in
              let uu____19002 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____18999 uu____19000 uu____19001 uu____19002
            else ());
           (let uu____19004 = head_matches_delta env1 wl1 t1 t2 in
            match uu____19004 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____19035, uu____19036) ->
                     let rec may_relate head =
                       let uu____19063 =
                         let uu____19064 = FStar_Syntax_Subst.compress head in
                         uu____19064.FStar_Syntax_Syntax.n in
                       match uu____19063 with
                       | FStar_Syntax_Syntax.Tm_name uu____19067 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____19068 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____19092 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____19092 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____19093 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____19094
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____19095 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____19097, uu____19098) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____19140) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____19146) ->
                           may_relate t
                       | uu____19151 -> false in
                     let uu____19152 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____19152 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____19162 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____19162
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____19168 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____19168
                          then
                            let uu____19169 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____19169 with
                             | (guard, wl2) ->
                                 let uu____19176 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____19176)
                          else
                            (let uu____19178 =
                               mklstr
                                 (fun uu____19189 ->
                                    let uu____19190 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____19191 =
                                      let uu____19192 =
                                        let uu____19195 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____19195
                                          (fun x ->
                                             let uu____19201 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____19201) in
                                      FStar_Util.dflt "" uu____19192 in
                                    let uu____19202 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____19203 =
                                      let uu____19204 =
                                        let uu____19207 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____19207
                                          (fun x ->
                                             let uu____19213 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____19213) in
                                      FStar_Util.dflt "" uu____19204 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____19190 uu____19191 uu____19202
                                      uu____19203) in
                             giveup env1 uu____19178 orig))
                 | (HeadMatch (true), uu____19214) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____19227 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____19227 with
                        | (guard, wl2) ->
                            let uu____19234 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____19234)
                     else
                       (let uu____19236 =
                          mklstr
                            (fun uu____19243 ->
                               let uu____19244 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____19245 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____19244 uu____19245) in
                        giveup env1 uu____19236 orig)
                 | (uu____19246, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2974_19260 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2974_19260.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2974_19260.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2974_19260.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2974_19260.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2974_19260.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2974_19260.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2974_19260.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2974_19260.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____19284 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____19284
          then
            let uu____19285 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____19285
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____19290 =
                let uu____19293 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19293 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____19290 t1);
             (let uu____19311 =
                let uu____19314 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19314 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____19311 t2);
             (let uu____19332 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____19332
              then
                let uu____19333 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____19334 =
                  let uu____19335 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____19336 =
                    let uu____19337 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____19337 in
                  Prims.op_Hat uu____19335 uu____19336 in
                let uu____19338 =
                  let uu____19339 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____19340 =
                    let uu____19341 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____19341 in
                  Prims.op_Hat uu____19339 uu____19340 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____19333 uu____19334 uu____19338
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____19344, uu____19345) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____19360, FStar_Syntax_Syntax.Tm_delayed uu____19361) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____19376, uu____19377) ->
                  let uu____19404 =
                    let uu___3005_19405 = problem in
                    let uu____19406 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3005_19405.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19406;
                      FStar_TypeChecker_Common.relation =
                        (uu___3005_19405.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3005_19405.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3005_19405.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3005_19405.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3005_19405.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3005_19405.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3005_19405.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3005_19405.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19404 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____19407, uu____19408) ->
                  let uu____19415 =
                    let uu___3011_19416 = problem in
                    let uu____19417 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3011_19416.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19417;
                      FStar_TypeChecker_Common.relation =
                        (uu___3011_19416.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3011_19416.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3011_19416.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3011_19416.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3011_19416.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3011_19416.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3011_19416.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3011_19416.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19415 wl
              | (uu____19418, FStar_Syntax_Syntax.Tm_ascribed uu____19419) ->
                  let uu____19446 =
                    let uu___3017_19447 = problem in
                    let uu____19448 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3017_19447.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3017_19447.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3017_19447.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19448;
                      FStar_TypeChecker_Common.element =
                        (uu___3017_19447.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3017_19447.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3017_19447.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3017_19447.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3017_19447.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3017_19447.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19446 wl
              | (uu____19449, FStar_Syntax_Syntax.Tm_meta uu____19450) ->
                  let uu____19457 =
                    let uu___3023_19458 = problem in
                    let uu____19459 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3023_19458.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3023_19458.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3023_19458.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19459;
                      FStar_TypeChecker_Common.element =
                        (uu___3023_19458.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3023_19458.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3023_19458.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3023_19458.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3023_19458.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3023_19458.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19457 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____19461),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____19463)) ->
                  let uu____19472 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____19472
              | (FStar_Syntax_Syntax.Tm_bvar uu____19473, uu____19474) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____19475, FStar_Syntax_Syntax.Tm_bvar uu____19476) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_19545 =
                    match uu___27_19545 with
                    | [] -> c
                    | bs ->
                        let uu____19573 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____19573 in
                  let uu____19584 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____19584 with
                   | ((bs11, c11), (bs21, c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst c11 in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst c21 in
                                  let rel =
                                    let uu____19733 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____19733
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_19818 =
                    match uu___28_19818 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____19860 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____19860 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____20005 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____20006 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____20005
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____20006 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____20007, uu____20008) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20037 -> true
                    | uu____20056 -> false in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3) in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____20109 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3125_20117 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3125_20117.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3125_20117.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3125_20117.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3125_20117.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3125_20117.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3125_20117.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3125_20117.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3125_20117.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3125_20117.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3125_20117.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3125_20117.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3125_20117.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3125_20117.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3125_20117.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3125_20117.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3125_20117.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3125_20117.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3125_20117.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3125_20117.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3125_20117.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3125_20117.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3125_20117.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3125_20117.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3125_20117.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3125_20117.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3125_20117.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3125_20117.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3125_20117.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3125_20117.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3125_20117.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3125_20117.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3125_20117.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3125_20117.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3125_20117.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3125_20117.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3125_20117.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3125_20117.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3125_20117.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3125_20117.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3125_20117.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3125_20117.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3125_20117.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3125_20117.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3125_20117.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____20109 with
                       | (uu____20120, ty, uu____20122) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____20131 =
                                 let uu____20132 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____20132.FStar_Syntax_Syntax.n in
                               match uu____20131 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20135 ->
                                   let uu____20142 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____20142
                               | uu____20143 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____20146 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____20146
                             then
                               let uu____20147 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____20148 =
                                 let uu____20149 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20149 in
                               let uu____20150 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20147 uu____20148 uu____20150
                             else ());
                            r1)) in
                  let uu____20152 =
                    let uu____20169 = maybe_eta t1 in
                    let uu____20176 = maybe_eta t2 in
                    (uu____20169, uu____20176) in
                  (match uu____20152 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3146_20218 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3146_20218.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3146_20218.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3146_20218.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3146_20218.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3146_20218.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3146_20218.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3146_20218.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3146_20218.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20239 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20239
                       then
                         let uu____20240 = destruct_flex_t not_abs wl in
                         (match uu____20240 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3163_20255 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3163_20255.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3163_20255.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3163_20255.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3163_20255.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3163_20255.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3163_20255.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3163_20255.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3163_20255.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20257 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20257 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20278 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20278
                       then
                         let uu____20279 = destruct_flex_t not_abs wl in
                         (match uu____20279 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3163_20294 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3163_20294.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3163_20294.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3163_20294.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3163_20294.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3163_20294.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3163_20294.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3163_20294.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3163_20294.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20296 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20296 orig))
                   | uu____20297 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____20314, FStar_Syntax_Syntax.Tm_abs uu____20315) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20344 -> true
                    | uu____20363 -> false in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3) in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____20416 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3125_20424 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3125_20424.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3125_20424.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3125_20424.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3125_20424.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3125_20424.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3125_20424.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3125_20424.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3125_20424.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3125_20424.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3125_20424.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3125_20424.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3125_20424.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3125_20424.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3125_20424.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3125_20424.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3125_20424.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3125_20424.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3125_20424.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3125_20424.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3125_20424.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3125_20424.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3125_20424.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3125_20424.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3125_20424.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3125_20424.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3125_20424.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3125_20424.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3125_20424.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3125_20424.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3125_20424.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3125_20424.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3125_20424.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3125_20424.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3125_20424.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3125_20424.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3125_20424.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3125_20424.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3125_20424.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3125_20424.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3125_20424.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3125_20424.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3125_20424.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3125_20424.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3125_20424.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____20416 with
                       | (uu____20427, ty, uu____20429) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____20438 =
                                 let uu____20439 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____20439.FStar_Syntax_Syntax.n in
                               match uu____20438 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20442 ->
                                   let uu____20449 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____20449
                               | uu____20450 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____20453 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____20453
                             then
                               let uu____20454 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____20455 =
                                 let uu____20456 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20456 in
                               let uu____20457 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20454 uu____20455 uu____20457
                             else ());
                            r1)) in
                  let uu____20459 =
                    let uu____20476 = maybe_eta t1 in
                    let uu____20483 = maybe_eta t2 in
                    (uu____20476, uu____20483) in
                  (match uu____20459 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3146_20525 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3146_20525.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3146_20525.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3146_20525.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3146_20525.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3146_20525.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3146_20525.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3146_20525.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3146_20525.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20546 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20546
                       then
                         let uu____20547 = destruct_flex_t not_abs wl in
                         (match uu____20547 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3163_20562 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3163_20562.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3163_20562.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3163_20562.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3163_20562.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3163_20562.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3163_20562.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3163_20562.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3163_20562.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20564 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20564 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20585 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20585
                       then
                         let uu____20586 = destruct_flex_t not_abs wl in
                         (match uu____20586 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3163_20601 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3163_20601.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3163_20601.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3163_20601.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3163_20601.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3163_20601.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3163_20601.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3163_20601.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3163_20601.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20603 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20603 orig))
                   | uu____20604 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____20633 =
                    let uu____20638 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____20638 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3186_20666 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3186_20666.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3186_20666.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3188_20668 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3188_20668.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3188_20668.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____20669, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3186_20683 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3186_20683.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3186_20683.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3188_20685 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3188_20685.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3188_20685.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____20686 -> (x1, x2) in
                  (match uu____20633 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____20705 = as_refinement false env t11 in
                       (match uu____20705 with
                        | (x12, phi11) ->
                            let uu____20712 = as_refinement false env t21 in
                            (match uu____20712 with
                             | (x22, phi21) ->
                                 ((let uu____20720 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____20720
                                   then
                                     ((let uu____20722 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____20723 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____20724 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____20722
                                         uu____20723 uu____20724);
                                      (let uu____20725 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____20726 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____20727 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____20725
                                         uu____20726 uu____20727))
                                   else ());
                                  (let uu____20729 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____20729 with
                                   | (base_prob, wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12 in
                                       let subst =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)] in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst phi11 in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst phi21 in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13 in
                                       let mk_imp imp phi13 phi23 =
                                         let uu____20797 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____20797
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____20809 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp FStar_Syntax_Util.mk_imp
                                               phi12 phi22 in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl in
                                         (let uu____20820 =
                                            let uu____20823 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20823 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____20820
                                            (p_guard base_prob));
                                         (let uu____20841 =
                                            let uu____20844 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20844 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____20841
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____20862 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____20862) in
                                       let has_uvars =
                                         (let uu____20866 =
                                            let uu____20867 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____20867 in
                                          Prims.op_Negation uu____20866) ||
                                           (let uu____20871 =
                                              let uu____20872 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____20872 in
                                            Prims.op_Negation uu____20871) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____20875 =
                                           let uu____20880 =
                                             let uu____20889 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____20889] in
                                           mk_t_problem wl1 uu____20880 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____20875 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____20911 =
                                                solve env1
                                                  (let uu___3231_20913 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3231_20913.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3231_20913.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3231_20913.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3231_20913.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3231_20913.tcenv);
                                                     wl_implicits =
                                                       (uu___3231_20913.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3231_20913.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____20911 with
                                               | Failed (prob, msg) ->
                                                   (FStar_Syntax_Unionfind.rollback
                                                      tx;
                                                    if
                                                      ((Prims.op_Negation
                                                          env1.FStar_TypeChecker_Env.uvar_subtyping)
                                                         && has_uvars)
                                                        ||
                                                        (Prims.op_Negation
                                                           wl2.smt_ok)
                                                    then giveup env1 msg prob
                                                    else fallback ())
                                               | Success
                                                   (uu____20924,
                                                    defer_to_tac,
                                                    uu____20926)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____20931 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____20931 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3247_20940 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3247_20940.attempting);
                                                         wl_deferred =
                                                           (uu___3247_20940.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3247_20940.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3247_20940.defer_ok);
                                                         smt_ok =
                                                           (uu___3247_20940.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3247_20940.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3247_20940.tcenv);
                                                         wl_implicits =
                                                           (uu___3247_20940.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3247_20940.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____20942 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____20942))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20944,
                 FStar_Syntax_Syntax.Tm_uvar uu____20945) ->
                  let uu____20970 = ensure_no_uvar_subst t1 wl in
                  (match uu____20970 with
                   | (t11, wl1) ->
                       let uu____20977 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20977 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20986;
                    FStar_Syntax_Syntax.pos = uu____20987;
                    FStar_Syntax_Syntax.vars = uu____20988;_},
                  uu____20989),
                 FStar_Syntax_Syntax.Tm_uvar uu____20990) ->
                  let uu____21039 = ensure_no_uvar_subst t1 wl in
                  (match uu____21039 with
                   | (t11, wl1) ->
                       let uu____21046 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21046 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____21055,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21056;
                    FStar_Syntax_Syntax.pos = uu____21057;
                    FStar_Syntax_Syntax.vars = uu____21058;_},
                  uu____21059)) ->
                  let uu____21108 = ensure_no_uvar_subst t1 wl in
                  (match uu____21108 with
                   | (t11, wl1) ->
                       let uu____21115 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21115 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21124;
                    FStar_Syntax_Syntax.pos = uu____21125;
                    FStar_Syntax_Syntax.vars = uu____21126;_},
                  uu____21127),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21128;
                    FStar_Syntax_Syntax.pos = uu____21129;
                    FStar_Syntax_Syntax.vars = uu____21130;_},
                  uu____21131)) ->
                  let uu____21204 = ensure_no_uvar_subst t1 wl in
                  (match uu____21204 with
                   | (t11, wl1) ->
                       let uu____21211 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21211 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____21220, uu____21221) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21234 = destruct_flex_t t1 wl in
                  (match uu____21234 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21241;
                    FStar_Syntax_Syntax.pos = uu____21242;
                    FStar_Syntax_Syntax.vars = uu____21243;_},
                  uu____21244),
                 uu____21245) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21282 = destruct_flex_t t1 wl in
                  (match uu____21282 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____21289, FStar_Syntax_Syntax.Tm_uvar uu____21290) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____21303, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21304;
                    FStar_Syntax_Syntax.pos = uu____21305;
                    FStar_Syntax_Syntax.vars = uu____21306;_},
                  uu____21307)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____21344,
                 FStar_Syntax_Syntax.Tm_arrow uu____21345) ->
                  solve_t' env
                    (let uu___3350_21373 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3350_21373.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3350_21373.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3350_21373.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3350_21373.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3350_21373.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3350_21373.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3350_21373.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3350_21373.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3350_21373.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21374;
                    FStar_Syntax_Syntax.pos = uu____21375;
                    FStar_Syntax_Syntax.vars = uu____21376;_},
                  uu____21377),
                 FStar_Syntax_Syntax.Tm_arrow uu____21378) ->
                  solve_t' env
                    (let uu___3350_21430 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3350_21430.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3350_21430.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3350_21430.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3350_21430.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3350_21430.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3350_21430.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3350_21430.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3350_21430.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3350_21430.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21431, FStar_Syntax_Syntax.Tm_uvar uu____21432) ->
                  let uu____21445 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21445
              | (uu____21446, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21447;
                    FStar_Syntax_Syntax.pos = uu____21448;
                    FStar_Syntax_Syntax.vars = uu____21449;_},
                  uu____21450)) ->
                  let uu____21487 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21487
              | (FStar_Syntax_Syntax.Tm_uvar uu____21488, uu____21489) ->
                  let uu____21502 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21502
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21503;
                    FStar_Syntax_Syntax.pos = uu____21504;
                    FStar_Syntax_Syntax.vars = uu____21505;_},
                  uu____21506),
                 uu____21507) ->
                  let uu____21544 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21544
              | (FStar_Syntax_Syntax.Tm_refine uu____21545, uu____21546) ->
                  let t21 =
                    let uu____21554 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____21554 in
                  solve_t env
                    (let uu___3385_21580 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3385_21580.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3385_21580.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3385_21580.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3385_21580.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3385_21580.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3385_21580.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3385_21580.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3385_21580.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3385_21580.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21581, FStar_Syntax_Syntax.Tm_refine uu____21582) ->
                  let t11 =
                    let uu____21590 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____21590 in
                  solve_t env
                    (let uu___3392_21616 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3392_21616.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3392_21616.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3392_21616.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3392_21616.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3392_21616.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3392_21616.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3392_21616.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3392_21616.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3392_21616.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____21698 =
                    let uu____21699 = guard_of_prob env wl problem t1 t2 in
                    match uu____21699 with
                    | (guard, wl1) ->
                        let uu____21706 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____21706 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____21925 = br1 in
                        (match uu____21925 with
                         | (p1, w1, uu____21954) ->
                             let uu____21971 = br2 in
                             (match uu____21971 with
                              | (p2, w2, uu____21994) ->
                                  let uu____21999 =
                                    let uu____22000 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____22000 in
                                  if uu____21999
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____22024 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____22024 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____22061 = br2 in
                                         (match uu____22061 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____22094 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____22094 in
                                              let uu____22099 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____22130,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____22151) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,
                                                   FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____22210 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____22210 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____22099
                                                (fun uu____22281 ->
                                                   match uu____22281 with
                                                   | (wprobs, wl2) ->
                                                       let uu____22318 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____22318
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____22338
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____22338
                                                              then
                                                                let uu____22339
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____22340
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____22339
                                                                  uu____22340
                                                              else ());
                                                             (let uu____22342
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____22342
                                                                (fun
                                                                   uu____22378
                                                                   ->
                                                                   match uu____22378
                                                                   with
                                                                   | 
                                                                   (r1, wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (((scope,
                                                                    prob) ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))))
                    | ([], []) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____22507 -> FStar_Pervasives_Native.None in
                  let uu____22548 = solve_branches wl brs1 brs2 in
                  (match uu____22548 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____22572 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____22572 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____22597 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____22597 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____22630 =
                                FStar_List.map
                                  (fun uu____22642 ->
                                     match uu____22642 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____22630 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____22651 =
                              let uu____22652 =
                                let uu____22653 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____22653
                                  (let uu___3491_22661 = wl3 in
                                   {
                                     attempting =
                                       (uu___3491_22661.attempting);
                                     wl_deferred =
                                       (uu___3491_22661.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3491_22661.wl_deferred_to_tac);
                                     ctr = (uu___3491_22661.ctr);
                                     defer_ok = (uu___3491_22661.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3491_22661.umax_heuristic_ok);
                                     tcenv = (uu___3491_22661.tcenv);
                                     wl_implicits =
                                       (uu___3491_22661.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3491_22661.repr_subcomp_allowed)
                                   }) in
                              solve env uu____22652 in
                            (match uu____22651 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____22666 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____22673 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____22673 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____22674, uu____22675) ->
                  let head1 =
                    let uu____22699 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22699
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22745 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22745
                      FStar_Pervasives_Native.fst in
                  ((let uu____22791 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22791
                    then
                      let uu____22792 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22793 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22794 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22792 uu____22793 uu____22794
                    else ());
                   (let no_free_uvars t =
                      (let uu____22804 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22804) &&
                        (let uu____22808 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22808) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____22824 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22824 = FStar_Syntax_Util.Equal in
                    let uu____22825 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22825
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22826 = equal t1 t2 in
                         (if uu____22826
                          then
                            let uu____22827 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22827
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22830 =
                            let uu____22837 = equal t1 t2 in
                            if uu____22837
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22847 = mk_eq2 wl env orig t1 t2 in
                               match uu____22847 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22830 with
                          | (guard, wl1) ->
                              let uu____22868 = solve_prob orig guard [] wl1 in
                              solve env uu____22868))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____22870, uu____22871) ->
                  let head1 =
                    let uu____22879 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22879
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22925 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22925
                      FStar_Pervasives_Native.fst in
                  ((let uu____22971 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22971
                    then
                      let uu____22972 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22973 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22974 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22972 uu____22973 uu____22974
                    else ());
                   (let no_free_uvars t =
                      (let uu____22984 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22984) &&
                        (let uu____22988 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22988) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____23004 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23004 = FStar_Syntax_Util.Equal in
                    let uu____23005 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23005
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23006 = equal t1 t2 in
                         (if uu____23006
                          then
                            let uu____23007 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23007
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23010 =
                            let uu____23017 = equal t1 t2 in
                            if uu____23017
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23027 = mk_eq2 wl env orig t1 t2 in
                               match uu____23027 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23010 with
                          | (guard, wl1) ->
                              let uu____23048 = solve_prob orig guard [] wl1 in
                              solve env uu____23048))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____23050, uu____23051) ->
                  let head1 =
                    let uu____23053 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23053
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23099 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23099
                      FStar_Pervasives_Native.fst in
                  ((let uu____23145 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23145
                    then
                      let uu____23146 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23147 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23148 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23146 uu____23147 uu____23148
                    else ());
                   (let no_free_uvars t =
                      (let uu____23158 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23158) &&
                        (let uu____23162 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23162) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____23178 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23178 = FStar_Syntax_Util.Equal in
                    let uu____23179 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23179
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23180 = equal t1 t2 in
                         (if uu____23180
                          then
                            let uu____23181 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23181
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23184 =
                            let uu____23191 = equal t1 t2 in
                            if uu____23191
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23201 = mk_eq2 wl env orig t1 t2 in
                               match uu____23201 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23184 with
                          | (guard, wl1) ->
                              let uu____23222 = solve_prob orig guard [] wl1 in
                              solve env uu____23222))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____23224, uu____23225) ->
                  let head1 =
                    let uu____23227 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23227
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23273 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23273
                      FStar_Pervasives_Native.fst in
                  ((let uu____23319 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23319
                    then
                      let uu____23320 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23321 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23322 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23320 uu____23321 uu____23322
                    else ());
                   (let no_free_uvars t =
                      (let uu____23332 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23332) &&
                        (let uu____23336 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23336) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____23352 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23352 = FStar_Syntax_Util.Equal in
                    let uu____23353 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23353
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23354 = equal t1 t2 in
                         (if uu____23354
                          then
                            let uu____23355 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23355
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23358 =
                            let uu____23365 = equal t1 t2 in
                            if uu____23365
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23375 = mk_eq2 wl env orig t1 t2 in
                               match uu____23375 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23358 with
                          | (guard, wl1) ->
                              let uu____23396 = solve_prob orig guard [] wl1 in
                              solve env uu____23396))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____23398, uu____23399) ->
                  let head1 =
                    let uu____23401 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23401
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23441 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23441
                      FStar_Pervasives_Native.fst in
                  ((let uu____23481 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23481
                    then
                      let uu____23482 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23483 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23484 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23482 uu____23483 uu____23484
                    else ());
                   (let no_free_uvars t =
                      (let uu____23494 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23494) &&
                        (let uu____23498 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23498) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____23514 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23514 = FStar_Syntax_Util.Equal in
                    let uu____23515 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23515
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23516 = equal t1 t2 in
                         (if uu____23516
                          then
                            let uu____23517 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23517
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23520 =
                            let uu____23527 = equal t1 t2 in
                            if uu____23527
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23537 = mk_eq2 wl env orig t1 t2 in
                               match uu____23537 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23520 with
                          | (guard, wl1) ->
                              let uu____23558 = solve_prob orig guard [] wl1 in
                              solve env uu____23558))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____23560, uu____23561) ->
                  let head1 =
                    let uu____23579 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23579
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23619 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23619
                      FStar_Pervasives_Native.fst in
                  ((let uu____23659 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23659
                    then
                      let uu____23660 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23661 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23662 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23660 uu____23661 uu____23662
                    else ());
                   (let no_free_uvars t =
                      (let uu____23672 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23672) &&
                        (let uu____23676 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23676) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____23692 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23692 = FStar_Syntax_Util.Equal in
                    let uu____23693 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23693
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23694 = equal t1 t2 in
                         (if uu____23694
                          then
                            let uu____23695 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23695
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23698 =
                            let uu____23705 = equal t1 t2 in
                            if uu____23705
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23715 = mk_eq2 wl env orig t1 t2 in
                               match uu____23715 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23698 with
                          | (guard, wl1) ->
                              let uu____23736 = solve_prob orig guard [] wl1 in
                              solve env uu____23736))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23738, FStar_Syntax_Syntax.Tm_match uu____23739) ->
                  let head1 =
                    let uu____23763 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23763
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23803 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23803
                      FStar_Pervasives_Native.fst in
                  ((let uu____23843 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23843
                    then
                      let uu____23844 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23845 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23846 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23844 uu____23845 uu____23846
                    else ());
                   (let no_free_uvars t =
                      (let uu____23856 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23856) &&
                        (let uu____23860 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23860) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____23876 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23876 = FStar_Syntax_Util.Equal in
                    let uu____23877 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23877
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23878 = equal t1 t2 in
                         (if uu____23878
                          then
                            let uu____23879 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23879
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23882 =
                            let uu____23889 = equal t1 t2 in
                            if uu____23889
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23899 = mk_eq2 wl env orig t1 t2 in
                               match uu____23899 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23882 with
                          | (guard, wl1) ->
                              let uu____23920 = solve_prob orig guard [] wl1 in
                              solve env uu____23920))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23922, FStar_Syntax_Syntax.Tm_uinst uu____23923) ->
                  let head1 =
                    let uu____23931 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23931
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23971 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23971
                      FStar_Pervasives_Native.fst in
                  ((let uu____24011 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24011
                    then
                      let uu____24012 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24013 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24014 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24012 uu____24013 uu____24014
                    else ());
                   (let no_free_uvars t =
                      (let uu____24024 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24024) &&
                        (let uu____24028 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24028) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____24044 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24044 = FStar_Syntax_Util.Equal in
                    let uu____24045 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24045
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24046 = equal t1 t2 in
                         (if uu____24046
                          then
                            let uu____24047 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24047
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24050 =
                            let uu____24057 = equal t1 t2 in
                            if uu____24057
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24067 = mk_eq2 wl env orig t1 t2 in
                               match uu____24067 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24050 with
                          | (guard, wl1) ->
                              let uu____24088 = solve_prob orig guard [] wl1 in
                              solve env uu____24088))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24090, FStar_Syntax_Syntax.Tm_name uu____24091) ->
                  let head1 =
                    let uu____24093 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24093
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24133 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24133
                      FStar_Pervasives_Native.fst in
                  ((let uu____24173 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24173
                    then
                      let uu____24174 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24175 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24176 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24174 uu____24175 uu____24176
                    else ());
                   (let no_free_uvars t =
                      (let uu____24186 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24186) &&
                        (let uu____24190 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24190) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____24206 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24206 = FStar_Syntax_Util.Equal in
                    let uu____24207 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24207
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24208 = equal t1 t2 in
                         (if uu____24208
                          then
                            let uu____24209 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24209
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24212 =
                            let uu____24219 = equal t1 t2 in
                            if uu____24219
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24229 = mk_eq2 wl env orig t1 t2 in
                               match uu____24229 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24212 with
                          | (guard, wl1) ->
                              let uu____24250 = solve_prob orig guard [] wl1 in
                              solve env uu____24250))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24252, FStar_Syntax_Syntax.Tm_constant uu____24253) ->
                  let head1 =
                    let uu____24255 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24255
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24295 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24295
                      FStar_Pervasives_Native.fst in
                  ((let uu____24335 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24335
                    then
                      let uu____24336 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24337 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24338 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24336 uu____24337 uu____24338
                    else ());
                   (let no_free_uvars t =
                      (let uu____24348 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24348) &&
                        (let uu____24352 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24352) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____24368 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24368 = FStar_Syntax_Util.Equal in
                    let uu____24369 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24369
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24370 = equal t1 t2 in
                         (if uu____24370
                          then
                            let uu____24371 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24371
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24374 =
                            let uu____24381 = equal t1 t2 in
                            if uu____24381
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24391 = mk_eq2 wl env orig t1 t2 in
                               match uu____24391 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24374 with
                          | (guard, wl1) ->
                              let uu____24412 = solve_prob orig guard [] wl1 in
                              solve env uu____24412))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24414, FStar_Syntax_Syntax.Tm_fvar uu____24415) ->
                  let head1 =
                    let uu____24417 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24417
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24463 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24463
                      FStar_Pervasives_Native.fst in
                  ((let uu____24509 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24509
                    then
                      let uu____24510 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24511 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24512 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24510 uu____24511 uu____24512
                    else ());
                   (let no_free_uvars t =
                      (let uu____24522 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24522) &&
                        (let uu____24526 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24526) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____24542 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24542 = FStar_Syntax_Util.Equal in
                    let uu____24543 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24543
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24544 = equal t1 t2 in
                         (if uu____24544
                          then
                            let uu____24545 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24545
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24548 =
                            let uu____24555 = equal t1 t2 in
                            if uu____24555
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24565 = mk_eq2 wl env orig t1 t2 in
                               match uu____24565 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24548 with
                          | (guard, wl1) ->
                              let uu____24586 = solve_prob orig guard [] wl1 in
                              solve env uu____24586))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24588, FStar_Syntax_Syntax.Tm_app uu____24589) ->
                  let head1 =
                    let uu____24607 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24607
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24647 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24647
                      FStar_Pervasives_Native.fst in
                  ((let uu____24687 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24687
                    then
                      let uu____24688 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24689 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24690 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24688 uu____24689 uu____24690
                    else ());
                   (let no_free_uvars t =
                      (let uu____24700 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24700) &&
                        (let uu____24704 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24704) in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11 in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21 in
                      let uu____24720 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24720 = FStar_Syntax_Util.Equal in
                    let uu____24721 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24721
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24722 = equal t1 t2 in
                         (if uu____24722
                          then
                            let uu____24723 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24723
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24726 =
                            let uu____24733 = equal t1 t2 in
                            if uu____24733
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24743 = mk_eq2 wl env orig t1 t2 in
                               match uu____24743 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24726 with
                          | (guard, wl1) ->
                              let uu____24764 = solve_prob orig guard [] wl1 in
                              solve env uu____24764))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____24766,
                 FStar_Syntax_Syntax.Tm_let uu____24767) ->
                  let uu____24792 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____24792
                  then
                    let uu____24793 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____24793
                  else
                    (let uu____24795 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____24795 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____24796, uu____24797) ->
                  let uu____24810 =
                    let uu____24815 =
                      let uu____24816 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24817 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24818 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24819 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24816 uu____24817 uu____24818 uu____24819 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24815) in
                  FStar_Errors.raise_error uu____24810
                    t1.FStar_Syntax_Syntax.pos
              | (uu____24820, FStar_Syntax_Syntax.Tm_let uu____24821) ->
                  let uu____24834 =
                    let uu____24839 =
                      let uu____24840 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24841 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24842 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24843 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24840 uu____24841 uu____24842 uu____24843 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24839) in
                  FStar_Errors.raise_error uu____24834
                    t1.FStar_Syntax_Syntax.pos
              | uu____24844 ->
                  let uu____24849 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____24849 orig))))
and (solve_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env ->
    fun problem ->
      fun wl ->
        let c1 = problem.FStar_TypeChecker_Common.lhs in
        let c2 = problem.FStar_TypeChecker_Common.rhs in
        let orig = FStar_TypeChecker_Common.CProb problem in
        let sub_prob wl1 t1 rel t2 reason =
          mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
            reason in
        let solve_eq c1_comp c2_comp g_lift =
          (let uu____24911 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____24911
           then
             let uu____24912 =
               let uu____24913 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____24913 in
             let uu____24914 =
               let uu____24915 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____24915 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____24912 uu____24914
           else ());
          (let uu____24917 =
             let uu____24918 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____24918 in
           if uu____24917
           then
             let uu____24919 =
               mklstr
                 (fun uu____24926 ->
                    let uu____24927 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____24928 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____24927 uu____24928) in
             giveup env uu____24919 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____24946 =
                  mklstr
                    (fun uu____24953 ->
                       let uu____24954 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____24955 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____24954 uu____24955) in
                giveup env uu____24946 orig)
             else
               (let uu____24957 =
                  FStar_List.fold_left2
                    (fun uu____24978 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____24978 with
                           | (univ_sub_probs, wl1) ->
                               let uu____24999 =
                                 let uu____25004 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____25005 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____25004
                                   FStar_TypeChecker_Common.EQ uu____25005
                                   "effect universes" in
                               (match uu____24999 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____24957 with
                | (univ_sub_probs, wl1) ->
                    let uu____25024 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____25024 with
                     | (ret_sub_prob, wl2) ->
                         let uu____25031 =
                           FStar_List.fold_right2
                             (fun uu____25068 ->
                                fun uu____25069 ->
                                  fun uu____25070 ->
                                    match (uu____25068, uu____25069,
                                            uu____25070)
                                    with
                                    | ((a1, uu____25114), (a2, uu____25116),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____25149 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____25149 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____25031 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____25175 =
                                  let uu____25178 =
                                    let uu____25181 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____25181 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____25178 in
                                FStar_List.append univ_sub_probs uu____25175 in
                              let guard =
                                let guard =
                                  let uu____25200 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____25200 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3644_25209 = wl3 in
                                {
                                  attempting = (uu___3644_25209.attempting);
                                  wl_deferred = (uu___3644_25209.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3644_25209.wl_deferred_to_tac);
                                  ctr = (uu___3644_25209.ctr);
                                  defer_ok = (uu___3644_25209.defer_ok);
                                  smt_ok = (uu___3644_25209.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3644_25209.umax_heuristic_ok);
                                  tcenv = (uu___3644_25209.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3644_25209.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____25211 = attempt sub_probs wl5 in
                              solve env uu____25211)))) in
        let solve_layered_sub c11 c21 =
          (let uu____25224 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____25224
           then
             let uu____25225 =
               let uu____25226 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25226
                 FStar_Syntax_Print.comp_to_string in
             let uu____25227 =
               let uu____25228 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25228
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____25225 uu____25227
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____25233 =
                 let uu____25234 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25234 FStar_Ident.string_of_id in
               let uu____25235 =
                 let uu____25236 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25236 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____25233 uu____25235 in
             let lift_c1 edge =
               let uu____25251 =
                 let uu____25256 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____25256
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____25251
                 (fun uu____25273 ->
                    match uu____25273 with
                    | (c, g) ->
                        let uu____25284 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____25284, g)) in
             let uu____25285 =
               let uu____25296 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____25296 with
               | FStar_Pervasives_Native.None ->
                   let uu____25309 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____25309 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____25325 = lift_c1 edge in
                        (match uu____25325 with
                         | (c12, g_lift) ->
                             let uu____25342 =
                               let uu____25345 =
                                 let uu____25346 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____25346
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____25345
                                 (fun ts ->
                                    let uu____25352 =
                                      let uu____25353 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____25353
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____25352
                                      (fun uu____25364 ->
                                         FStar_Pervasives_Native.Some
                                           uu____25364)) in
                             (c12, g_lift, uu____25342, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____25368 =
                     let uu____25371 =
                       let uu____25372 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____25372
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____25371
                       (fun uu____25383 ->
                          FStar_Pervasives_Native.Some uu____25383) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____25368,
                     true) in
             match uu____25285 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____25394 =
                     mklstr
                       (fun uu____25401 ->
                          let uu____25402 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____25403 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____25402 uu____25403) in
                   giveup env uu____25394 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3679_25409 = wl in
                      {
                        attempting = (uu___3679_25409.attempting);
                        wl_deferred = (uu___3679_25409.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3679_25409.wl_deferred_to_tac);
                        ctr = (uu___3679_25409.ctr);
                        defer_ok = (uu___3679_25409.defer_ok);
                        smt_ok = (uu___3679_25409.smt_ok);
                        umax_heuristic_ok =
                          (uu___3679_25409.umax_heuristic_ok);
                        tcenv = (uu___3679_25409.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3679_25409.repr_subcomp_allowed)
                      } in
                    let uu____25410 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____25432 =
                             let uu____25433 = FStar_Syntax_Subst.compress t in
                             uu____25433.FStar_Syntax_Syntax.n in
                           match uu____25432 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____25436 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____25450)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____25456) ->
                               is_uvar t1
                           | uu____25481 -> false in
                         FStar_List.fold_right2
                           (fun uu____25514 ->
                              fun uu____25515 ->
                                fun uu____25516 ->
                                  match (uu____25514, uu____25515,
                                          uu____25516)
                                  with
                                  | ((a1, uu____25560), (a2, uu____25562),
                                     (is_sub_probs, wl2)) ->
                                      let uu____25595 = is_uvar a1 in
                                      if uu____25595
                                      then
                                        ((let uu____25603 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____25603
                                          then
                                            let uu____25604 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____25605 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____25604 uu____25605
                                          else ());
                                         (let uu____25607 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____25607 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____25410 with
                    | (is_sub_probs, wl2) ->
                        let uu____25633 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____25633 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____25646 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____25647 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____25646 s uu____25647 in
                             let uu____25648 =
                               let uu____25677 =
                                 let uu____25678 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____25678.FStar_Syntax_Syntax.n in
                               match uu____25677 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____25737 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____25737 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____25800 =
                                          let uu____25819 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____25819
                                            (fun uu____25922 ->
                                               match uu____25922 with
                                               | (l1, l2) ->
                                                   let uu____25995 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____25995)) in
                                        (match uu____25800 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____26100 ->
                                   let uu____26101 =
                                     let uu____26106 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____26106) in
                                   FStar_Errors.raise_error uu____26101 r in
                             (match uu____25648 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____26179 =
                                    let uu____26186 =
                                      let uu____26187 =
                                        let uu____26188 =
                                          let uu____26195 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____26195,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____26188 in
                                      [uu____26187] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____26186
                                      (fun b ->
                                         let uu____26211 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____26212 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____26213 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____26211 uu____26212
                                           uu____26213) r in
                                  (match uu____26179 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3744_26221 = wl3 in
                                         {
                                           attempting =
                                             (uu___3744_26221.attempting);
                                           wl_deferred =
                                             (uu___3744_26221.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3744_26221.wl_deferred_to_tac);
                                           ctr = (uu___3744_26221.ctr);
                                           defer_ok =
                                             (uu___3744_26221.defer_ok);
                                           smt_ok = (uu___3744_26221.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3744_26221.umax_heuristic_ok);
                                           tcenv = (uu___3744_26221.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3744_26221.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____26246 =
                                                  let uu____26253 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____26253, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____26246) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____26270 =
                                         let f_sort_is =
                                           let uu____26280 =
                                             let uu____26283 =
                                               let uu____26284 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____26284.FStar_Syntax_Syntax.sort in
                                             let uu____26293 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____26294 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____26283 uu____26293 r
                                               uu____26294 in
                                           FStar_All.pipe_right uu____26280
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____26299 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____26335 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____26335 with
                                                  | (ps, wl5) ->
                                                      ((let uu____26357 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____26357
                                                        then
                                                          let uu____26358 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____26359 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____26358
                                                            uu____26359
                                                        else ());
                                                       (let uu____26361 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____26361
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____26299 in
                                       (match uu____26270 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____26385 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____26385
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____26386 =
                                              let g_sort_is =
                                                let uu____26396 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____26397 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____26396 r uu____26397 in
                                              let uu____26398 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____26434 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____26434 with
                                                       | (ps, wl6) ->
                                                           ((let uu____26456
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____26456
                                                             then
                                                               let uu____26457
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____26458
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____26457
                                                                 uu____26458
                                                             else ());
                                                            (let uu____26460
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____26460
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____26398 in
                                            (match uu____26386 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____26486 =
                                                     let uu____26491 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____26492 =
                                                       let uu____26493 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____26493 in
                                                     (uu____26491,
                                                       uu____26492) in
                                                   match uu____26486 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____26521 =
                                                     let uu____26524 =
                                                       let uu____26527 =
                                                         let uu____26530 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____26530 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____26527 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____26524 in
                                                   ret_sub_prob ::
                                                     uu____26521 in
                                                 let guard =
                                                   let guard =
                                                     let uu____26551 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____26551 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____26562 =
                                                     let uu____26565 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____26568 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____26568)
                                                       uu____26565 in
                                                   solve_prob orig
                                                     uu____26562 [] wl6 in
                                                 let uu____26569 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____26569))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____26594 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____26596 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____26596]
               | x -> x in
             let c12 =
               let uu___3802_26599 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3802_26599.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3802_26599.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3802_26599.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3802_26599.FStar_Syntax_Syntax.flags)
               } in
             let uu____26600 =
               let uu____26605 =
                 FStar_All.pipe_right
                   (let uu___3805_26607 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3805_26607.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3805_26607.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3805_26607.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3805_26607.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____26605
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____26600
               (fun uu____26621 ->
                  match uu____26621 with
                  | (c, g) ->
                      let uu____26628 =
                        let uu____26629 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____26629 in
                      if uu____26628
                      then
                        let uu____26630 =
                          let uu____26635 =
                            let uu____26636 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____26637 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____26636 uu____26637 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____26635) in
                        FStar_Errors.raise_error uu____26630 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____26639 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____26641 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____26641))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____26639
           then
             let uu____26642 =
               mklstr
                 (fun uu____26649 ->
                    let uu____26650 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____26651 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____26650 uu____26651) in
             giveup env uu____26642 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_26657 ->
                        match uu___29_26657 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____26658 -> false)) in
              let uu____26659 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____26689)::uu____26690,
                   (wp2, uu____26692)::uu____26693) -> (wp1, wp2)
                | uu____26766 ->
                    let uu____26791 =
                      let uu____26796 =
                        let uu____26797 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____26798 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____26797 uu____26798 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____26796) in
                    FStar_Errors.raise_error uu____26791
                      env.FStar_TypeChecker_Env.range in
              match uu____26659 with
              | (wpc1, wpc2) ->
                  let uu____26805 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____26805
                  then
                    let uu____26806 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____26806 wl
                  else
                    (let uu____26808 =
                       let uu____26815 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____26815 in
                     match uu____26808 with
                     | (c2_decl, qualifiers) ->
                         let uu____26836 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____26836
                         then
                           let c1_repr =
                             let uu____26840 =
                               let uu____26841 =
                                 let uu____26842 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____26842 in
                               let uu____26843 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26841 uu____26843 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26840 in
                           let c2_repr =
                             let uu____26845 =
                               let uu____26846 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____26847 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26846 uu____26847 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26845 in
                           let uu____26848 =
                             let uu____26853 =
                               let uu____26854 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____26855 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____26854 uu____26855 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____26853 in
                           (match uu____26848 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____26859 = attempt [prob] wl2 in
                                solve env uu____26859)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____26876 = lift_c1 () in
                                   FStar_All.pipe_right uu____26876
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____26898 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____26898
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____26902 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____26902 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____26908 =
                                       let uu____26909 =
                                         let uu____26926 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____26929 =
                                           let uu____26940 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____26940; wpc1_2] in
                                         (uu____26926, uu____26929) in
                                       FStar_Syntax_Syntax.Tm_app uu____26909 in
                                     FStar_Syntax_Syntax.mk uu____26908 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____26988 =
                                      let uu____26989 =
                                        let uu____27006 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____27009 =
                                          let uu____27020 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____27029 =
                                            let uu____27040 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____27040; wpc1_2] in
                                          uu____27020 :: uu____27029 in
                                        (uu____27006, uu____27009) in
                                      FStar_Syntax_Syntax.Tm_app uu____26989 in
                                    FStar_Syntax_Syntax.mk uu____26988 r)) in
                            (let uu____27094 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____27094
                             then
                               let uu____27095 =
                                 let uu____27096 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____27096 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____27095
                             else ());
                            (let uu____27098 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____27098 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____27106 =
                                     let uu____27109 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____27112 ->
                                          FStar_Pervasives_Native.Some
                                            uu____27112) uu____27109 in
                                   solve_prob orig uu____27106 [] wl1 in
                                 let uu____27113 = attempt [base_prob] wl2 in
                                 solve env uu____27113))))) in
        let uu____27114 = FStar_Util.physical_equality c1 c2 in
        if uu____27114
        then
          let uu____27115 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____27115
        else
          ((let uu____27118 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____27118
            then
              let uu____27119 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____27120 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____27119
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____27120
            else ());
           (let uu____27122 =
              let uu____27131 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____27134 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____27131, uu____27134) in
            match uu____27122 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____27152),
                    FStar_Syntax_Syntax.Total (t2, uu____27154)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____27171 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27171 wl
                 | (FStar_Syntax_Syntax.GTotal uu____27172,
                    FStar_Syntax_Syntax.Total uu____27173) ->
                     let uu____27190 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____27190 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____27192),
                    FStar_Syntax_Syntax.Total (t2, uu____27194)) ->
                     let uu____27211 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27211 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____27213),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27215)) ->
                     let uu____27232 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27232 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27234),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27236)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____27253 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27253 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27255),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27257)) ->
                     let uu____27274 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____27274 orig
                 | (FStar_Syntax_Syntax.GTotal uu____27275,
                    FStar_Syntax_Syntax.Comp uu____27276) ->
                     let uu____27285 =
                       let uu___3929_27288 = problem in
                       let uu____27291 =
                         let uu____27292 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27292 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3929_27288.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27291;
                         FStar_TypeChecker_Common.relation =
                           (uu___3929_27288.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3929_27288.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3929_27288.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3929_27288.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3929_27288.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3929_27288.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3929_27288.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3929_27288.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27285 wl
                 | (FStar_Syntax_Syntax.Total uu____27293,
                    FStar_Syntax_Syntax.Comp uu____27294) ->
                     let uu____27303 =
                       let uu___3929_27306 = problem in
                       let uu____27309 =
                         let uu____27310 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27310 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3929_27306.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27309;
                         FStar_TypeChecker_Common.relation =
                           (uu___3929_27306.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3929_27306.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3929_27306.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3929_27306.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3929_27306.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3929_27306.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3929_27306.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3929_27306.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27303 wl
                 | (FStar_Syntax_Syntax.Comp uu____27311,
                    FStar_Syntax_Syntax.GTotal uu____27312) ->
                     let uu____27321 =
                       let uu___3941_27324 = problem in
                       let uu____27327 =
                         let uu____27328 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27328 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3941_27324.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3941_27324.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3941_27324.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27327;
                         FStar_TypeChecker_Common.element =
                           (uu___3941_27324.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3941_27324.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3941_27324.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3941_27324.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3941_27324.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3941_27324.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27321 wl
                 | (FStar_Syntax_Syntax.Comp uu____27329,
                    FStar_Syntax_Syntax.Total uu____27330) ->
                     let uu____27339 =
                       let uu___3941_27342 = problem in
                       let uu____27345 =
                         let uu____27346 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27346 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3941_27342.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3941_27342.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3941_27342.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27345;
                         FStar_TypeChecker_Common.element =
                           (uu___3941_27342.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3941_27342.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3941_27342.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3941_27342.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3941_27342.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3941_27342.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27339 wl
                 | (FStar_Syntax_Syntax.Comp uu____27347,
                    FStar_Syntax_Syntax.Comp uu____27348) ->
                     let uu____27349 =
                       (((FStar_Syntax_Util.is_ml_comp c11) &&
                           (FStar_Syntax_Util.is_ml_comp c21))
                          ||
                          ((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_total_comp c21)))
                         ||
                         (((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_ml_comp c21))
                            &&
                            (problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB)) in
                     if uu____27349
                     then
                       let uu____27350 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____27350 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27354 =
                            let uu____27359 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____27359
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27365 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____27366 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____27365, uu____27366)) in
                          match uu____27354 with
                          | (c1_comp1, c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                                FStar_TypeChecker_Env.trivial_guard
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11 in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21 in
                           (let uu____27373 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____27373
                            then
                              let uu____27374 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____27375 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____27374 uu____27375
                            else ());
                           (let uu____27377 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____27377
                            then solve_layered_sub c12 c22
                            else
                              (let uu____27379 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____27379 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____27382 =
                                     mklstr
                                       (fun uu____27389 ->
                                          let uu____27390 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____27391 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____27390 uu____27391) in
                                   giveup env uu____27382 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____27398 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____27398 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____27439 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____27439 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____27457 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27485 ->
                match uu____27485 with
                | (u1, u2) ->
                    let uu____27492 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____27493 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____27492 uu____27493)) in
      FStar_All.pipe_right uu____27457 (FStar_String.concat ", ") in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
let (guard_to_string :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> Prims.string)
  =
  fun env ->
    fun g ->
      match ((g.FStar_TypeChecker_Common.guard_f),
              (g.FStar_TypeChecker_Common.deferred),
              (g.FStar_TypeChecker_Common.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial, [], (uu____27520, [])) when
          let uu____27545 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____27545 -> "{}"
      | uu____27546 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27569 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____27569
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____27589 =
              FStar_List.map
                (fun uu____27600 ->
                   match uu____27600 with
                   | (msg, x) ->
                       let uu____27607 =
                         let uu____27608 = prob_to_string env x in
                         Prims.op_Hat ": " uu____27608 in
                       Prims.op_Hat msg uu____27607) defs in
            FStar_All.pipe_right uu____27589 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____27612 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____27613 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____27614 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____27612 uu____27613 uu____27614 imps
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Range.range -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl ->
    fun env ->
      fun lhs ->
        fun rel ->
          fun rhs ->
            fun elt ->
              fun loc ->
                let reason =
                  let uu____27667 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____27667
                  then
                    let uu____27668 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____27669 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27668
                      (rel_to_string rel) uu____27669
                  else "TOP" in
                let uu____27671 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____27671 with
                | (p, wl1) ->
                    (def_check_prob (Prims.op_Hat "new_t_problem." reason)
                       (FStar_TypeChecker_Common.TProb p);
                     ((FStar_TypeChecker_Common.TProb p), wl1))
let (new_t_prob :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv *
              worklist))
  =
  fun wl ->
    fun env ->
      fun t1 ->
        fun rel ->
          fun t2 ->
            let x =
              let uu____27729 =
                let uu____27732 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____27735 ->
                     FStar_Pervasives_Native.Some uu____27735) uu____27732 in
              FStar_Syntax_Syntax.new_bv uu____27729 t1 in
            let uu____27736 =
              let uu____27741 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27741 in
            match uu____27736 with | (p, wl1) -> (p, x, wl1)
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * lstring) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option)
  =
  fun env ->
    fun probs ->
      fun err ->
        let tx = FStar_Syntax_Unionfind.new_transaction () in
        (let uu____27812 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____27812
         then
           let uu____27813 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____27813
         else ());
        (let uu____27817 =
           FStar_Util.record_time (fun uu____27823 -> solve env probs) in
         match uu____27817 with
         | (sol, ms) ->
             ((let uu____27835 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____27835
               then
                 let uu____27836 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____27836
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____27849 =
                     FStar_Util.record_time
                       (fun uu____27855 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____27849 with
                    | ((), ms1) ->
                        ((let uu____27866 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____27866
                          then
                            let uu____27867 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____27867
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____27878 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____27878
                     then
                       let uu____27879 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____27879
                     else ());
                    (let result = err (d, s) in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____27903 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____27903
            then
              let uu____27904 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27904
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____27908 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____27908
             then
               let uu____27909 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27909
             else ());
            (let f2 =
               let uu____27912 =
                 let uu____27913 = FStar_Syntax_Util.unmeta f1 in
                 uu____27913.FStar_Syntax_Syntax.n in
               match uu____27912 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27917 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4061_27918 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4061_27918.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4061_27918.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4061_27918.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4061_27918.FStar_TypeChecker_Common.implicits)
             })))
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred
        * FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
        -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun prob ->
      fun dopt ->
        match dopt with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred, defer_to_tac, implicits) ->
            let uu____27969 =
              let uu____27970 =
                let uu____27971 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____27972 ->
                       FStar_TypeChecker_Common.NonTrivial uu____27972) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____27971;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____27970 in
            FStar_All.pipe_left
              (fun uu____27979 -> FStar_Pervasives_Native.Some uu____27979)
              uu____27969
let with_guard_no_simp :
  'uuuuuu27988 .
    'uuuuuu27988 ->
      FStar_TypeChecker_Common.prob ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
          -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env ->
    fun prob ->
      fun dopt ->
        match dopt with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred, defer_to_tac, implicits) ->
            let uu____28037 =
              let uu____28038 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____28039 ->
                     FStar_TypeChecker_Common.NonTrivial uu____28039) in
              {
                FStar_TypeChecker_Common.guard_f = uu____28038;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____28037
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok ->
    fun env ->
      fun t1 ->
        fun t2 ->
          (let uu____28069 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____28069
           then
             let uu____28070 = FStar_Syntax_Print.term_to_string t1 in
             let uu____28071 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____28070
               uu____28071
           else ());
          (let uu____28073 =
             let uu____28078 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____28078 in
           match uu____28073 with
           | (prob, wl) ->
               let g =
                 let uu____28086 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____28096 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____28086 in
               ((let uu____28118 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____28118
                 then
                   let uu____28119 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____28119
                 else ());
                g))
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____28136 = try_teq true env t1 t2 in
        match uu____28136 with
        | FStar_Pervasives_Native.None ->
            ((let uu____28140 = FStar_TypeChecker_Env.get_range env in
              let uu____28141 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____28140 uu____28141);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____28148 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____28148
              then
                let uu____28149 = FStar_Syntax_Print.term_to_string t1 in
                let uu____28150 = FStar_Syntax_Print.term_to_string t2 in
                let uu____28151 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____28149
                  uu____28150 uu____28151
              else ());
             g)
let (get_teq_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____28171 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____28171
         then
           let uu____28172 = FStar_Syntax_Print.term_to_string t1 in
           let uu____28173 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____28172
             uu____28173
         else ());
        (let uu____28175 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____28175 with
         | (prob, x, wl) ->
             let g =
               let uu____28190 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____28200 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____28190 in
             ((let uu____28222 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____28222
               then
                 let uu____28223 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____28223
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____28228 =
                     let uu____28229 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____28229 g1 in
                   FStar_Pervasives_Native.Some uu____28228)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____28250 = FStar_TypeChecker_Env.get_range env in
          let uu____28251 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____28250 uu____28251
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun c1 ->
      fun c2 ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB in
        (let uu____28276 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____28276
         then
           let uu____28277 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____28278 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28277 uu____28278
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28281 =
           let uu____28288 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28288 "sub_comp" in
         match uu____28281 with
         | (prob, wl) ->
             let wl1 =
               let uu___4134_28298 = wl in
               {
                 attempting = (uu___4134_28298.attempting);
                 wl_deferred = (uu___4134_28298.wl_deferred);
                 wl_deferred_to_tac = (uu___4134_28298.wl_deferred_to_tac);
                 ctr = (uu___4134_28298.ctr);
                 defer_ok = (uu___4134_28298.defer_ok);
                 smt_ok = (uu___4134_28298.smt_ok);
                 umax_heuristic_ok = (uu___4134_28298.umax_heuristic_ok);
                 tcenv = (uu___4134_28298.tcenv);
                 wl_implicits = (uu___4134_28298.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____28301 =
                 FStar_Util.record_time
                   (fun uu____28312 ->
                      let uu____28313 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____28323 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____28313) in
               match uu____28301 with
               | (r, ms) ->
                   ((let uu____28353 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____28353
                     then
                       let uu____28354 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____28355 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____28356 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28354 uu____28355
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28356
                     else ());
                    r))))
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> unit)
  =
  fun tx ->
    fun env ->
      fun uu____28385 ->
        match uu____28385 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28428 =
                 let uu____28433 =
                   let uu____28434 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____28435 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28434 uu____28435 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28433) in
               let uu____28436 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____28428 uu____28436) in
            let equiv v v' =
              let uu____28448 =
                let uu____28453 = FStar_Syntax_Subst.compress_univ v in
                let uu____28454 = FStar_Syntax_Subst.compress_univ v' in
                (uu____28453, uu____28454) in
              match uu____28448 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28477 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____28507 = FStar_Syntax_Subst.compress_univ v in
                      match uu____28507 with
                      | FStar_Syntax_Syntax.U_unif uu____28514 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28545 ->
                                    match uu____28545 with
                                    | (u, v') ->
                                        let uu____28554 = equiv v v' in
                                        if uu____28554
                                        then
                                          let uu____28557 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____28557 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____28573 -> [])) in
            let uu____28578 =
              let wl =
                let uu___4177_28582 = empty_worklist env in
                {
                  attempting = (uu___4177_28582.attempting);
                  wl_deferred = (uu___4177_28582.wl_deferred);
                  wl_deferred_to_tac = (uu___4177_28582.wl_deferred_to_tac);
                  ctr = (uu___4177_28582.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4177_28582.smt_ok);
                  umax_heuristic_ok = (uu___4177_28582.umax_heuristic_ok);
                  tcenv = (uu___4177_28582.tcenv);
                  wl_implicits = (uu___4177_28582.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4177_28582.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28600 ->
                      match uu____28600 with
                      | (lb, v) ->
                          let uu____28607 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____28607 with
                           | USolved wl1 -> ()
                           | uu____28609 -> fail lb v))) in
            let rec check_ineq uu____28619 =
              match uu____28619 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____28628) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____28655,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____28657,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____28670) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____28677, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____28685 -> false) in
            let uu____28690 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28705 ->
                      match uu____28705 with
                      | (u, v) ->
                          let uu____28712 = check_ineq (u, v) in
                          if uu____28712
                          then true
                          else
                            ((let uu____28715 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____28715
                              then
                                let uu____28716 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____28717 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____28716
                                  uu____28717
                              else ());
                             false))) in
            if uu____28690
            then ()
            else
              ((let uu____28721 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____28721
                then
                  ((let uu____28723 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28723);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28733 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28733))
                else ());
               (let uu____28743 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28743))
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> unit)
  =
  fun env ->
    fun ineqs ->
      let tx = FStar_Syntax_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
let (try_solve_deferred_constraints :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok ->
    fun smt_ok ->
      fun env ->
        fun g ->
          let fail uu____28817 =
            match uu____28817 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4255_28842 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4255_28842.attempting);
              wl_deferred = (uu___4255_28842.wl_deferred);
              wl_deferred_to_tac = (uu___4255_28842.wl_deferred_to_tac);
              ctr = (uu___4255_28842.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4255_28842.umax_heuristic_ok);
              tcenv = (uu___4255_28842.tcenv);
              wl_implicits = (uu___4255_28842.wl_implicits);
              repr_subcomp_allowed = (uu___4255_28842.repr_subcomp_allowed)
            } in
          (let uu____28844 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____28844
           then
             let uu____28845 = FStar_Util.string_of_bool defer_ok in
             let uu____28846 = wl_to_string wl in
             let uu____28847 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____28845 uu____28846 uu____28847
           else ());
          (let g1 =
             let uu____28850 = solve_and_commit env wl fail in
             match uu____28850 with
             | FStar_Pervasives_Native.Some
                 (uu____28859::uu____28860, uu____28861, uu____28862) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4272_28892 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4272_28892.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4272_28892.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____28897 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____28909 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____28909
             then
               let uu____28910 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____28910
             else ());
            (let uu___4280_28912 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4280_28912.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4280_28912.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4280_28912.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4280_28912.FStar_TypeChecker_Common.implicits)
             })))
let (solve_deferred_constraints' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun smt_ok ->
    fun env -> fun g -> try_solve_deferred_constraints false smt_ok env g
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env -> fun g -> solve_deferred_constraints' true env g
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env -> fun g -> try_solve_deferred_constraints true true env g
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg ->
    fun env ->
      fun g ->
        fun use_smt ->
          let debug =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac")) in
          (let uu____28987 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____28987
           then
             let uu____28988 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____28988
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4297_28992 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4297_28992.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4297_28992.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4297_28992.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4297_28992.FStar_TypeChecker_Common.implicits)
             } in
           let uu____28993 =
             let uu____28994 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____28994 in
           if uu____28993
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____29002 = FStar_TypeChecker_Env.get_range env in
                      let uu____29003 =
                        let uu____29004 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____29004 in
                      FStar_Errors.diag uu____29002 uu____29003)
                   else ();
                   (let vc1 =
                      let uu____29007 =
                        let uu____29010 =
                          let uu____29011 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____29011 in
                        FStar_Pervasives_Native.Some uu____29010 in
                      FStar_Profiling.profile
                        (fun uu____29013 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____29007 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____29015 = FStar_TypeChecker_Env.get_range env in
                       let uu____29016 =
                         let uu____29017 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____29017 in
                       FStar_Errors.diag uu____29015 uu____29016)
                    else ();
                    (let uu____29020 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____29020 "discharge_guard'" env vc1);
                    (let uu____29021 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____29021 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____29028 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____29029 =
                                 let uu____29030 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____29030 in
                               FStar_Errors.diag uu____29028 uu____29029)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____29035 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____29036 =
                                 let uu____29037 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____29037 in
                               FStar_Errors.diag uu____29035 uu____29036)
                            else ();
                            (let vcs =
                               let uu____29048 = FStar_Options.use_tactics () in
                               if uu____29048
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____29068 ->
                                      (let uu____29070 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____29071 -> ()) uu____29070);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____29114 ->
                                               match uu____29114 with
                                               | (env1, goal, opts) ->
                                                   let uu____29130 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____29130, opts)))))
                               else
                                 (let uu____29132 =
                                    let uu____29139 = FStar_Options.peek () in
                                    (env, vc2, uu____29139) in
                                  [uu____29132]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____29172 ->
                                     match uu____29172 with
                                     | (env1, goal, opts) ->
                                         let uu____29182 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____29182 with
                                          | FStar_TypeChecker_Common.Trivial
                                              ->
                                              if debug
                                              then
                                                FStar_Util.print_string
                                                  "Goal completely solved by tactic\n"
                                              else ()
                                          | FStar_TypeChecker_Common.NonTrivial
                                              goal1 ->
                                              (FStar_Options.push ();
                                               FStar_Options.set opts;
                                               if debug
                                               then
                                                 (let uu____29189 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____29190 =
                                                    let uu____29191 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____29192 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____29191 uu____29192 in
                                                  FStar_Errors.diag
                                                    uu____29189 uu____29190)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____29195 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____29196 =
                                                    let uu____29197 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____29197 in
                                                  FStar_Errors.diag
                                                    uu____29195 uu____29196)
                                               else ();
                                               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                 use_env_range_msg env1 goal1;
                                               FStar_Options.pop ())))));
                            FStar_Pervasives_Native.Some ret_g))))))
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____29211 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____29211 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____29218 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29218
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____29229 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____29229 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29255 = try_teq false env t1 t2 in
        match uu____29255 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
let (try_solve_single_valued_implicits :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_TypeChecker_Env.implicits ->
        (FStar_TypeChecker_Env.implicits * Prims.bool))
  =
  fun env ->
    fun is_tac ->
      fun imps ->
        if is_tac
        then (imps, false)
        else
          (let imp_value imp =
             let uu____29298 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____29298 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____29308 =
                   let uu____29309 = FStar_Syntax_Subst.compress t_norm in
                   uu____29309.FStar_Syntax_Syntax.n in
                 (match uu____29308 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____29315 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29315
                        (fun uu____29318 ->
                           FStar_Pervasives_Native.Some uu____29318)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____29320) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____29325 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29325
                        (fun uu____29328 ->
                           FStar_Pervasives_Native.Some uu____29328)
                  | uu____29329 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____29339 =
                      let uu____29340 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____29340 FStar_Util.is_none in
                    if uu____29339
                    then
                      let uu____29345 = imp_value imp in
                      match uu____29345 with
                      | FStar_Pervasives_Native.Some tm ->
                          (commit
                             [TERM
                                ((imp.FStar_TypeChecker_Common.imp_uvar), tm)];
                           true)
                      | FStar_Pervasives_Native.None -> b
                    else b) false imps in
           (imps, b))
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun is_tac ->
      fun g ->
        let uu____29366 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____29366 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____29384 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____29384 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____29388 ->
                       let uu____29389 =
                         let uu____29390 = FStar_Syntax_Subst.compress r in
                         uu____29390.FStar_Syntax_Syntax.n in
                       (match uu____29389 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____29394)
                            -> unresolved ctx_u'
                        | uu____29411 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____29431 = acc in
              match uu____29431 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____29438 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____29438 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____29451 = hd in
                       (match uu____29451 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____29457 = unresolved ctx_u in
                               if uu____29457
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____29466 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____29466
                                       then
                                         let uu____29467 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____29467
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____29473 =
                                           teq_nosmt env1 t tm in
                                         match uu____29473 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4442_29482 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4442_29482.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4442_29482.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4442_29482.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4442_29482.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4442_29482.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4442_29482.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4442_29482.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4445_29484 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4445_29484.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4445_29484.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4445_29484.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____29485 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4450_29491 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4450_29491.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4450_29491.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4450_29491.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4450_29491.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4450_29491.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4450_29491.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4450_29491.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4450_29491.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4450_29491.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4450_29491.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4450_29491.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4450_29491.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4450_29491.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4450_29491.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4450_29491.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4450_29491.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4450_29491.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4450_29491.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4450_29491.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4450_29491.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4450_29491.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4450_29491.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4450_29491.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4450_29491.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4450_29491.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4450_29491.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4450_29491.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4450_29491.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4450_29491.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4450_29491.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4450_29491.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4450_29491.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4450_29491.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4450_29491.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4450_29491.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4450_29491.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4450_29491.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4455_29494 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4455_29494.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4455_29494.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4455_29494.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4455_29494.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4455_29494.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4455_29494.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4455_29494.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4455_29494.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4455_29494.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4455_29494.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4455_29494.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4455_29494.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4455_29494.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4455_29494.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4455_29494.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4455_29494.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4455_29494.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4455_29494.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4455_29494.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4455_29494.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4455_29494.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4455_29494.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4455_29494.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4455_29494.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4455_29494.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4455_29494.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4455_29494.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4455_29494.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4455_29494.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4455_29494.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4455_29494.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4455_29494.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____29497 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29497
                                     then
                                       let uu____29498 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____29499 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____29500 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____29501 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____29498 uu____29499 uu____29500
                                         reason uu____29501
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4461_29505 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____29512 =
                                               let uu____29521 =
                                                 let uu____29528 =
                                                   let uu____29529 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____29530 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____29531 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____29529 uu____29530
                                                     uu____29531 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____29528, r) in
                                               [uu____29521] in
                                             FStar_Errors.add_errors
                                               uu____29512);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____29545 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____29555 ->
                                                 let uu____29556 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____29557 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____29558 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____29556 uu____29557
                                                   reason uu____29558)) env2
                                           g1 true in
                                       match uu____29545 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4473_29560 = g in
            let uu____29561 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4473_29560.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4473_29560.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4473_29560.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4473_29560.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____29561
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____29573 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29573
       then
         let uu____29574 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____29574
       else ());
      resolve_implicits' env false g
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env -> fun g -> resolve_implicits' env true g
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env ->
    fun g ->
      (let uu____29597 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29597
       then
         let uu____29598 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____29598
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____29602 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____29603 -> ()) uu____29602
       | imp::uu____29605 ->
           let uu____29608 =
             let uu____29613 =
               let uu____29614 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____29615 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____29614 uu____29615
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29613) in
           FStar_Errors.raise_error uu____29608
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29631 = teq env t1 t2 in
        force_trivial_guard env uu____29631
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29647 = teq_nosmt env t1 t2 in
        match uu____29647 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
let (layered_effect_teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.string FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        fun reason ->
          (let uu____29677 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____29677
           then
             let uu____29678 =
               let uu____29679 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____29679
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____29685 = FStar_Syntax_Print.term_to_string t1 in
             let uu____29686 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____29678
               uu____29685 uu____29686
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4511_29698 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4511_29698.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4511_29698.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4511_29698.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4511_29698.FStar_TypeChecker_Common.implicits)
      }
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Common.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____29733 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29733
         then
           let uu____29734 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29735 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29734
             uu____29735
         else ());
        (let uu____29737 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29737 with
         | (prob, x, wl) ->
             let g =
               let uu____29756 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29766 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29756 in
             ((let uu____29788 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____29788
               then
                 let uu____29789 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____29790 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____29791 =
                   let uu____29792 = FStar_Util.must g in
                   guard_to_string env uu____29792 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29789 uu____29790 uu____29791
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29826 = check_subtyping env t1 t2 in
        match uu____29826 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29845 =
              let uu____29846 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____29846 g in
            FStar_Pervasives_Native.Some uu____29845
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29864 = check_subtyping env t1 t2 in
        match uu____29864 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29883 =
              let uu____29884 =
                let uu____29885 = FStar_Syntax_Syntax.mk_binder x in
                [uu____29885] in
              FStar_TypeChecker_Env.close_guard env uu____29884 g in
            FStar_Pervasives_Native.Some uu____29883
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____29922 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29922
         then
           let uu____29923 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29924 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____29923
             uu____29924
         else ());
        (let uu____29926 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29926 with
         | (prob, x, wl) ->
             let g =
               let uu____29941 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____29951 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29941 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____29976 =
                      let uu____29977 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____29977] in
                    FStar_TypeChecker_Env.close_guard env uu____29976 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____30014 = subtype_nosmt env t1 t2 in
        match uu____30014 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)