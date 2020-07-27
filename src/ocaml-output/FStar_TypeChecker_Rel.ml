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
                              (FStar_All.pipe_right
                                 src.FStar_Syntax_Syntax.ctx_uvar_binders
                                 (FStar_List.existsb
                                    (fun uu____5943 ->
                                       match uu____5943 with
                                       | (bv2, uu____5951) ->
                                           FStar_Syntax_Syntax.bv_eq bv1 bv2)))
                                &&
                                (let uu____5957 =
                                   FStar_All.pipe_right pfx
                                     (FStar_List.existsb
                                        (fun uu____5975 ->
                                           match uu____5975 with
                                           | (bv2, uu____5983) ->
                                               FStar_Syntax_Syntax.bv_eq bv1
                                                 bv2)) in
                                 Prims.op_Negation uu____5957))) in
                if (FStar_List.length bs1) = Prims.int_zero
                then
                  aux src.FStar_Syntax_Syntax.ctx_uvar_typ (fun src' -> src')
                else
                  (let uu____5997 =
                     let uu____5998 =
                       let uu____6001 =
                         let uu____6004 =
                           FStar_All.pipe_right
                             src.FStar_Syntax_Syntax.ctx_uvar_typ
                             (env.FStar_TypeChecker_Env.universe_of env) in
                         FStar_All.pipe_right uu____6004
                           (fun uu____6007 ->
                              FStar_Pervasives_Native.Some uu____6007) in
                       FStar_All.pipe_right uu____6001
                         (FStar_Syntax_Syntax.mk_Total'
                            src.FStar_Syntax_Syntax.ctx_uvar_typ) in
                     FStar_All.pipe_right uu____5998
                       (FStar_Syntax_Util.arrow bs1) in
                   aux uu____5997
                     (fun src' ->
                        let uu____6017 =
                          let uu____6018 =
                            FStar_All.pipe_right bs1
                              FStar_Syntax_Syntax.binders_to_names in
                          FStar_All.pipe_right uu____6018
                            (FStar_List.map FStar_Syntax_Syntax.as_arg) in
                        FStar_Syntax_Syntax.mk_Tm_app src' uu____6017
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
                 | uu____6143 -> out) FStar_Syntax_Syntax.no_names g in
        let uu____6144 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6208 ->
                  fun uu____6209 ->
                    match (uu____6208, uu____6209) with
                    | ((isect, isect_set), (x, imp)) ->
                        let uu____6312 =
                          let uu____6313 = FStar_Util.set_mem x v1_set in
                          FStar_All.pipe_left Prims.op_Negation uu____6313 in
                        if uu____6312
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6342 =
                             FStar_Util.set_is_subset_of fvs isect_set in
                           if uu____6342
                           then
                             let uu____6357 = FStar_Util.set_add x isect_set in
                             (((x, imp) :: isect), uu____6357)
                           else (isect, isect_set))) ([], ctx_binders)) in
        match uu____6144 with | (isect, uu____6406) -> FStar_List.rev isect
let binders_eq :
  'uuuuuu6441 'uuuuuu6442 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6441) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6442) Prims.list -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6499 ->
              fun uu____6500 ->
                match (uu____6499, uu____6500) with
                | ((a, uu____6518), (b, uu____6520)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let name_exists_in_binders :
  'uuuuuu6535 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6535) Prims.list -> Prims.bool
  =
  fun x ->
    fun bs ->
      FStar_Util.for_some
        (fun uu____6565 ->
           match uu____6565 with
           | (y, uu____6571) -> FStar_Syntax_Syntax.bv_eq x y) bs
let pat_vars :
  'uuuuuu6580 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6580) Prims.list ->
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
                   let uu____6742 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu____6742
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6772 -> FStar_Pervasives_Native.None) in
        aux [] args
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu____6819 -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch _0 -> true | uu____6856 -> false
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee -> match projectee with | HeadMatch _0 -> _0
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | FullMatch -> true | uu____6868 -> false
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_6873 ->
    match uu___19_6873 with
    | MisMatch (d1, d2) ->
        let uu____6884 =
          let uu____6885 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu____6886 =
            let uu____6887 =
              let uu____6888 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.op_Hat uu____6888 ")" in
            Prims.op_Hat ") (" uu____6887 in
          Prims.op_Hat uu____6885 uu____6886 in
        Prims.op_Hat "MisMatch (" uu____6884
    | HeadMatch u ->
        let uu____6890 = FStar_Util.string_of_bool u in
        Prims.op_Hat "HeadMatch " uu____6890
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___20_6895 ->
    match uu___20_6895 with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu____6910 -> HeadMatch false
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____6923 =
            (let uu____6928 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
             let uu____6929 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu____6928 = uu____6929) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) in
          if uu____6923 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____6932 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6932 with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6943 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6966 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6975 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6993 = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu____6993
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6994 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6995 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6996 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7009 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7022 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____7046) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____7052, uu____7053) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu____7095) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7120;
             FStar_Syntax_Syntax.index = uu____7121;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____7123)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7130 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7131 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7132 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7147 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7154 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7174 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____7174
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
           { FStar_Syntax_Syntax.blob = uu____7192;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7193;
             FStar_Syntax_Syntax.ltyp = uu____7194;
             FStar_Syntax_Syntax.rng = uu____7195;_},
           uu____7196) ->
            let uu____7207 = FStar_Syntax_Util.unlazy t11 in
            head_matches env uu____7207 t21
        | (uu____7208, FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7209;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7210;
             FStar_Syntax_Syntax.ltyp = uu____7211;
             FStar_Syntax_Syntax.rng = uu____7212;_})
            ->
            let uu____7223 = FStar_Syntax_Util.unlazy t21 in
            head_matches env t11 uu____7223
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7226 = FStar_Syntax_Syntax.bv_eq x y in
            if uu____7226
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7234 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____7234
            then FullMatch
            else
              (let uu____7236 =
                 let uu____7245 =
                   let uu____7248 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____7248 in
                 let uu____7249 =
                   let uu____7252 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____7252 in
                 (uu____7245, uu____7249) in
               MisMatch uu____7236)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu____7258),
           FStar_Syntax_Syntax.Tm_uinst (g, uu____7260)) ->
            let uu____7269 = head_matches env f g in
            FStar_All.pipe_right uu____7269 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           uu____7270) -> HeadMatch true
        | (uu____7271, FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify)) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7274 = FStar_Const.eq_const c d in
            if uu____7274
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu____7281),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu____7283)) ->
            let uu____7316 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head in
            if uu____7316
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7323),
           FStar_Syntax_Syntax.Tm_refine (y, uu____7325)) ->
            let uu____7334 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7334 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7336), uu____7337) ->
            let uu____7342 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____7342 head_match
        | (uu____7343, FStar_Syntax_Syntax.Tm_refine (x, uu____7345)) ->
            let uu____7350 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7350 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7351,
           FStar_Syntax_Syntax.Tm_type uu____7352) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow uu____7353,
           FStar_Syntax_Syntax.Tm_arrow uu____7354) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7384),
           FStar_Syntax_Syntax.Tm_app (head', uu____7386)) ->
            let uu____7435 = head_matches env head head' in
            FStar_All.pipe_right uu____7435 head_match
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7437), uu____7438) ->
            let uu____7463 = head_matches env head t21 in
            FStar_All.pipe_right uu____7463 head_match
        | (uu____7464, FStar_Syntax_Syntax.Tm_app (head, uu____7466)) ->
            let uu____7491 = head_matches env t11 head in
            FStar_All.pipe_right uu____7491 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7492, FStar_Syntax_Syntax.Tm_let
           uu____7493) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match uu____7518,
           FStar_Syntax_Syntax.Tm_match uu____7519) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7564, FStar_Syntax_Syntax.Tm_abs
           uu____7565) -> HeadMatch true
        | uu____7602 ->
            let uu____7607 =
              let uu____7616 = delta_depth_of_term env t11 in
              let uu____7619 = delta_depth_of_term env t21 in
              (uu____7616, uu____7619) in
            MisMatch uu____7607
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
              let uu____7687 = unrefine env t in
              FStar_Syntax_Util.head_of uu____7687 in
            (let uu____7689 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7689
             then
               let uu____7690 = FStar_Syntax_Print.term_to_string t in
               let uu____7691 = FStar_Syntax_Print.term_to_string head in
               FStar_Util.print2 "Head of %s is %s\n" uu____7690 uu____7691
             else ());
            (let uu____7693 =
               let uu____7694 = FStar_Syntax_Util.un_uinst head in
               uu____7694.FStar_Syntax_Syntax.n in
             match uu____7693 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7700 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 (match uu____7700 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu____7714 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta") in
                        if uu____7714
                        then
                          let uu____7715 =
                            FStar_Syntax_Print.term_to_string head in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7715
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7717 ->
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
                      let uu____7732 =
                        let uu____7733 = FStar_Syntax_Util.eq_tm t t' in
                        uu____7733 = FStar_Syntax_Util.Equal in
                      if uu____7732
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7738 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta") in
                          if uu____7738
                          then
                            let uu____7739 =
                              FStar_Syntax_Print.term_to_string t in
                            let uu____7740 =
                              FStar_Syntax_Print.term_to_string t' in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7739
                              uu____7740
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7742 -> FStar_Pervasives_Native.None) in
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
            (let uu____7880 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7880
             then
               let uu____7881 = FStar_Syntax_Print.term_to_string t11 in
               let uu____7882 = FStar_Syntax_Print.term_to_string t21 in
               let uu____7883 = string_of_match_result r in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7881
                 uu____7882 uu____7883
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
               let uu____7907 =
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
               match uu____7907 with
               | (t12, t22) -> aux retry (n_delta + Prims.int_one) t12 t22 in
             let reduce_both_and_try_again d r1 =
               let uu____7952 = FStar_TypeChecker_Common.decr_delta_depth d in
               match uu____7952 with
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
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7984),
                  uu____7985)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8003 =
                      let uu____8012 = maybe_inline t11 in
                      let uu____8015 = maybe_inline t21 in
                      (uu____8012, uu____8015) in
                    match uu____8003 with
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
                 (uu____8052, FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8053))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8071 =
                      let uu____8080 = maybe_inline t11 in
                      let uu____8083 = maybe_inline t21 in
                      (uu____8080, uu____8083) in
                    match uu____8071 with
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
             | MisMatch uu____8132 -> fail n_delta r t11 t21
             | uu____8141 -> success n_delta r t11 t21) in
          let r = aux true Prims.int_zero t1 t2 in
          (let uu____8154 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu____8154
           then
             let uu____8155 = FStar_Syntax_Print.term_to_string t1 in
             let uu____8156 = FStar_Syntax_Print.term_to_string t2 in
             let uu____8157 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             let uu____8164 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8176 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must in
                  FStar_All.pipe_right uu____8176
                    (fun uu____8210 ->
                       match uu____8210 with
                       | (t11, t21) ->
                           let uu____8217 =
                             FStar_Syntax_Print.term_to_string t11 in
                           let uu____8218 =
                             let uu____8219 =
                               FStar_Syntax_Print.term_to_string t21 in
                             Prims.op_Hat "; " uu____8219 in
                           Prims.op_Hat uu____8217 uu____8218)) in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8155 uu____8156 uu____8157 uu____8164
           else ());
          r
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____8231 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____8231 FStar_Pervasives_Native.fst
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8244 ->
    match uu___21_8244 with
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
      let uu___1279_8281 = p in
      let uu____8284 = whnf tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8285 = whnf tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1279_8281.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8284;
        FStar_TypeChecker_Common.relation =
          (uu___1279_8281.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8285;
        FStar_TypeChecker_Common.element =
          (uu___1279_8281.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1279_8281.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1279_8281.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1279_8281.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1279_8281.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1279_8281.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8299 = compress_tprob tcenv p1 in
          FStar_All.pipe_right uu____8299
            (fun uu____8304 -> FStar_TypeChecker_Common.TProb uu____8304)
      | FStar_TypeChecker_Common.CProb uu____8305 -> p
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv ->
    fun pr ->
      let prob =
        let uu____8327 = compress_prob tcenv pr in
        FStar_All.pipe_right uu____8327 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8335 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8335 with
           | (lh, lhs_args) ->
               let uu____8382 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8382 with
                | (rh, rhs_args) ->
                    let uu____8429 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8442,
                         FStar_Syntax_Syntax.Tm_uvar uu____8443) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8532 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8559, uu____8560)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8575, FStar_Syntax_Syntax.Tm_uvar uu____8576)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8591,
                         FStar_Syntax_Syntax.Tm_arrow uu____8592) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1330_8622 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1330_8622.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1330_8622.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1330_8622.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1330_8622.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1330_8622.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1330_8622.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1330_8622.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1330_8622.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1330_8622.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8625,
                         FStar_Syntax_Syntax.Tm_type uu____8626) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1330_8642 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1330_8642.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1330_8642.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1330_8642.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1330_8642.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1330_8642.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1330_8642.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1330_8642.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1330_8642.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1330_8642.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type uu____8645,
                         FStar_Syntax_Syntax.Tm_uvar uu____8646) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1330_8662 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1330_8662.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1330_8662.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1330_8662.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1330_8662.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1330_8662.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1330_8662.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1330_8662.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1330_8662.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1330_8662.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8665, FStar_Syntax_Syntax.Tm_uvar uu____8666)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8681, uu____8682)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8697, FStar_Syntax_Syntax.Tm_uvar uu____8698)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8713, uu____8714) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu____8429 with
                     | (rank, tp1) ->
                         let uu____8727 =
                           FStar_All.pipe_right
                             (let uu___1350_8731 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1350_8731.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1350_8731.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1350_8731.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1350_8731.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1350_8731.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1350_8731.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1350_8731.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1350_8731.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1350_8731.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____8734 ->
                                FStar_TypeChecker_Common.TProb uu____8734) in
                         (rank, uu____8727))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8738 =
            FStar_All.pipe_right
              (let uu___1354_8742 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1354_8742.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1354_8742.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1354_8742.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1354_8742.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1354_8742.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1354_8742.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1354_8742.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1354_8742.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1354_8742.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____8745 -> FStar_TypeChecker_Common.CProb uu____8745) in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8738)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    let rec aux uu____8804 probs =
      match uu____8804 with
      | (min_rank, min, out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some p,
                   FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8885 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____8906 = rank wl.tcenv hd in
               (match uu____8906 with
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
                      (let uu____8965 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8969 = FStar_Option.get min_rank in
                            rank_less_than rank1 uu____8969) in
                       if uu____8965
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
          let uu____9037 = FStar_Syntax_Util.head_and_args t in
          match uu____9037 with
          | (hd, uu____9055) ->
              let uu____9080 =
                let uu____9081 = FStar_Syntax_Subst.compress hd in
                uu____9081.FStar_Syntax_Syntax.n in
              (match uu____9080 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu____9085) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9119 ->
                           match uu____9119 with
                           | (y, uu____9127) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9149 ->
                                       match uu____9149 with
                                       | (x, uu____9157) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9162 -> false) in
        let uu____9163 = rank tcenv p in
        match uu____9163 with
        | (r, p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9170 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9202 -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | USolved _0 -> true | uu____9215 -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UFailed _0 -> true | uu____9228 -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s -> let uu____9240 = FStar_Thunk.mkv s in UFailed uu____9240
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu____9251 = mklstr s in UFailed uu____9251
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
                        let uu____9296 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____9296 with
                        | (k, uu____9302) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9314 -> false)))
            | uu____9315 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu____9367 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2 -> FStar_Syntax_Util.eq_univs uv1 uv2)) in
                        if uu____9367 then uv1 :: uvs else uvs) []) in
            let filter =
              FStar_List.filter
                (fun u ->
                   let uu____9387 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u' -> FStar_Syntax_Util.eq_univs u u')) in
                   Prims.op_Negation uu____9387) in
            let uu____9392 = filter u12 in
            let uu____9395 = filter u22 in (uu____9392, uu____9395) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9425 = filter_out_common_univs us1 us2 in
                   (match uu____9425 with
                    | (us11, us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13, u23::us23) ->
                                let uu____9484 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23 in
                                (match uu____9484 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9487 -> USolved wl1 in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9503 ->
                               let uu____9504 =
                                 FStar_Syntax_Print.univ_to_string u12 in
                               let uu____9505 =
                                 FStar_Syntax_Print.univ_to_string u22 in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9504 uu____9505))
               | (FStar_Syntax_Syntax.U_max us, u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9529 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9529 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | (u', FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9555 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9555 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | uu____9558 ->
                   ufailed_thunk
                     (fun uu____9569 ->
                        let uu____9570 =
                          FStar_Syntax_Print.univ_to_string u12 in
                        let uu____9571 =
                          FStar_Syntax_Print.univ_to_string u22 in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____9570 uu____9571 msg)) in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9572, uu____9573) ->
              let uu____9574 =
                let uu____9575 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9576 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9575 uu____9576 in
              failwith uu____9574
          | (FStar_Syntax_Syntax.U_unknown, uu____9577) ->
              let uu____9578 =
                let uu____9579 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9580 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9579 uu____9580 in
              failwith uu____9578
          | (uu____9581, FStar_Syntax_Syntax.U_bvar uu____9582) ->
              let uu____9583 =
                let uu____9584 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9585 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9584 uu____9585 in
              failwith uu____9583
          | (uu____9586, FStar_Syntax_Syntax.U_unknown) ->
              let uu____9587 =
                let uu____9588 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9589 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9588 uu____9589 in
              failwith uu____9587
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              let uu____9592 =
                let uu____9593 = FStar_Ident.string_of_id x in
                let uu____9594 = FStar_Ident.string_of_id y in
                uu____9593 = uu____9594 in
              if uu____9592
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9620 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9620
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu____9636 = occurs_univ v1 u3 in
              if uu____9636
              then
                let uu____9637 =
                  let uu____9638 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9639 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9638 uu____9639 in
                try_umax_components u11 u21 uu____9637
              else
                (let uu____9641 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9641)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9655 = occurs_univ v1 u3 in
              if uu____9655
              then
                let uu____9656 =
                  let uu____9657 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9658 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9657 uu____9658 in
                try_umax_components u11 u21 uu____9656
              else
                (let uu____9660 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9660)
          | (FStar_Syntax_Syntax.U_max uu____9661, uu____9662) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9668 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9668
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9670, FStar_Syntax_Syntax.U_max uu____9671) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9677 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9677
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9679,
             FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9680,
             FStar_Syntax_Syntax.U_name uu____9681) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ
             uu____9682) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name
             uu____9683) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9684,
             FStar_Syntax_Syntax.U_succ uu____9685) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9686,
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
      let uu____9786 = bc1 in
      match uu____9786 with
      | (bs1, mk_cod1) ->
          let uu____9830 = bc2 in
          (match uu____9830 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu____9941 = aux xs ys in
                     (match uu____9941 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu____10024 =
                       let uu____10031 = mk_cod1 xs in ([], uu____10031) in
                     let uu____10034 =
                       let uu____10041 = mk_cod2 ys in ([], uu____10041) in
                     (uu____10024, uu____10034) in
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
                  let uu____10109 = FStar_Syntax_Syntax.bv_to_name t in
                  FStar_Syntax_Util.mk_has_type t11 uu____10109 t21
              | FStar_Pervasives_Native.None ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11 in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11 in
                  let uu____10112 =
                    let uu____10113 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Util.mk_has_type t11 uu____10113 t21 in
                  FStar_Syntax_Util.mk_forall u_x x uu____10112 in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB ->
                let uu____10118 = has_type_guard t1 t2 in (uu____10118, wl)
            | FStar_TypeChecker_Common.SUBINV ->
                let uu____10119 = has_type_guard t2 t1 in (uu____10119, wl)
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_10124 ->
    match uu___22_10124 with
    | Flex (uu____10125, uu____10126, []) -> true
    | uu____10135 -> false
let (should_defer_flex_to_user_tac :
  FStar_TypeChecker_Env.env -> worklist -> flex_t -> Prims.bool) =
  fun env ->
    fun wl ->
      fun f ->
        let uu____10151 = f in
        match uu____10151 with
        | Flex (uu____10152, u, uu____10154) ->
            let b =
              FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                wl.tcenv u in
            ((let uu____10157 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ResolveImplicitsHook") in
              if uu____10157
              then
                let uu____10158 =
                  FStar_Syntax_Print.ctx_uvar_to_string_no_reason u in
                let uu____10159 = FStar_Util.string_of_bool b in
                FStar_Util.print2
                  "Rel.should_defer_flex_to_user_tac for %s returning %s\n"
                  uu____10158 uu____10159
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
      let uu____10183 = f in
      match uu____10183 with
      | Flex
          (uu____10190,
           { FStar_Syntax_Syntax.ctx_uvar_head = uu____10191;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10192;
             FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
             FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____10195;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____10196;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____10197;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____10198;_},
           args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10262 ->
                 match uu____10262 with
                 | (y, uu____10270) -> FStar_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu____10424 =
                  let uu____10439 =
                    let uu____10442 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10442 in
                  ((FStar_List.rev pat_binders), uu____10439) in
                FStar_Pervasives_Native.Some uu____10424
            | (uu____10475, []) ->
                let uu____10506 =
                  let uu____10521 =
                    let uu____10524 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10524 in
                  ((FStar_List.rev pat_binders), uu____10521) in
                FStar_Pervasives_Native.Some uu____10506
            | ((formal, formal_imp)::formals1, (a, a_imp)::args2) ->
                let uu____10615 =
                  let uu____10616 = FStar_Syntax_Subst.compress a in
                  uu____10616.FStar_Syntax_Syntax.n in
                (match uu____10615 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____10636 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders) in
                     if uu____10636
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1695_10663 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1695_10663.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1695_10663.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          } in
                        let subst =
                          let uu____10667 =
                            let uu____10668 =
                              let uu____10675 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              (formal, uu____10675) in
                            FStar_Syntax_Syntax.NT uu____10668 in
                          [uu____10667] in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1 in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res in
                        aux
                          (((let uu___1701_10691 = x1 in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1701_10691.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1701_10691.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10692 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([], args2) ->
                let uu____10732 =
                  let uu____10739 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStar_Syntax_Util.arrow_formals uu____10739 in
                (match uu____10732 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10798 ->
                          aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10823 ->
               let uu____10824 = FStar_Syntax_Util.arrow_formals t_hd in
               (match uu____10824 with
                | (formals, t_res) -> aux [] formals t_res args))
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu____11153 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel") in
       if uu____11153
       then
         let uu____11154 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11154
       else ());
      (let uu____11157 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace") in
       if uu____11157
       then
         let uu____11158 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11158
       else ());
      (let uu____11160 = next_prob probs in
       match uu____11160 with
       | FStar_Pervasives_Native.Some (hd, tl, rank1) ->
           let probs1 =
             let uu___1728_11187 = probs in
             {
               attempting = tl;
               wl_deferred = (uu___1728_11187.wl_deferred);
               wl_deferred_to_tac = (uu___1728_11187.wl_deferred_to_tac);
               ctr = (uu___1728_11187.ctr);
               defer_ok = (uu___1728_11187.defer_ok);
               smt_ok = (uu___1728_11187.smt_ok);
               umax_heuristic_ok = (uu___1728_11187.umax_heuristic_ok);
               tcenv = (uu___1728_11187.tcenv);
               wl_implicits = (uu___1728_11187.wl_implicits);
               repr_subcomp_allowed = (uu___1728_11187.repr_subcomp_allowed)
             } in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11195 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs in
                 if uu____11195
                 then
                   let uu____11196 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                   solve env uu____11196
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
                           (let uu___1740_11201 = tp in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1740_11201.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1740_11201.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1740_11201.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1740_11201.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1740_11201.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1740_11201.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1740_11201.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1740_11201.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1740_11201.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None ->
           (match probs.wl_deferred with
            | [] ->
                let uu____11219 =
                  let uu____11226 = as_deferred probs.wl_deferred_to_tac in
                  ([], uu____11226, (probs.wl_implicits)) in
                Success uu____11219
            | uu____11231 ->
                let uu____11240 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11299 ->
                          match uu____11299 with
                          | (c, uu____11307, uu____11308) -> c < probs.ctr)) in
                (match uu____11240 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11349 =
                            let uu____11356 = as_deferred probs.wl_deferred in
                            let uu____11357 =
                              as_deferred probs.wl_deferred_to_tac in
                            (uu____11356, uu____11357, (probs.wl_implicits)) in
                          Success uu____11349
                      | uu____11358 ->
                          let uu____11367 =
                            let uu___1754_11368 = probs in
                            let uu____11369 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11388 ->
                                      match uu____11388 with
                                      | (uu____11395, uu____11396, y) -> y)) in
                            {
                              attempting = uu____11369;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1754_11368.wl_deferred_to_tac);
                              ctr = (uu___1754_11368.ctr);
                              defer_ok = (uu___1754_11368.defer_ok);
                              smt_ok = (uu___1754_11368.smt_ok);
                              umax_heuristic_ok =
                                (uu___1754_11368.umax_heuristic_ok);
                              tcenv = (uu___1754_11368.tcenv);
                              wl_implicits = (uu___1754_11368.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1754_11368.repr_subcomp_allowed)
                            } in
                          solve env uu____11367))))
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
            let uu____11403 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____11403 with
            | USolved wl1 ->
                let uu____11405 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____11405
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11408 = defer_lit "" orig wl1 in
                solve env uu____11408
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
                  let uu____11458 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____11458 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11461 -> ufailed_simple "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11473;
                  FStar_Syntax_Syntax.vars = uu____11474;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11477;
                  FStar_Syntax_Syntax.vars = uu____11478;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11490, uu____11491) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11498, FStar_Syntax_Syntax.Tm_uinst uu____11499) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11506 -> USolved wl
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
            ((let uu____11516 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____11516
              then
                let uu____11517 = prob_to_string env orig in
                let uu____11518 = FStar_Thunk.force msg in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11517 uu____11518
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
          (let uu____11526 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____11526
           then
             let uu____11527 = prob_to_string env orig in
             FStar_Util.print1 "\n\t\tDeferring %s to a tactic\n" uu____11527
           else ());
          (let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
           let wl2 =
             let uu___1838_11531 = wl1 in
             let uu____11532 =
               let uu____11541 =
                 let uu____11548 = FStar_Thunk.mkv reason in
                 ((wl1.ctr), uu____11548, orig) in
               uu____11541 :: (wl1.wl_deferred_to_tac) in
             {
               attempting = (uu___1838_11531.attempting);
               wl_deferred = (uu___1838_11531.wl_deferred);
               wl_deferred_to_tac = uu____11532;
               ctr = (uu___1838_11531.ctr);
               defer_ok = (uu___1838_11531.defer_ok);
               smt_ok = (uu___1838_11531.smt_ok);
               umax_heuristic_ok = (uu___1838_11531.umax_heuristic_ok);
               tcenv = (uu___1838_11531.tcenv);
               wl_implicits = (uu___1838_11531.wl_implicits);
               repr_subcomp_allowed = (uu___1838_11531.repr_subcomp_allowed)
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
                let uu____11571 = FStar_Syntax_Util.head_and_args t in
                match uu____11571 with
                | (head, uu____11593) ->
                    let uu____11618 =
                      let uu____11619 = FStar_Syntax_Subst.compress head in
                      uu____11619.FStar_Syntax_Syntax.n in
                    (match uu____11618 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu____11627) ->
                         let uu____11644 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu____11644,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____11645 -> (false, "")) in
              let uu____11646 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu____11646 with
               | (l1, r1) ->
                   let uu____11653 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu____11653 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____11661 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl in
                           solve env uu____11661)))
          | uu____11662 ->
              let uu____11663 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu____11663
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
               let uu____11747 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu____11747 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu____11800 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu____11800
                then
                  let uu____11801 = FStar_Syntax_Print.term_to_string t1 in
                  let uu____11802 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____11801 uu____11802
                else ());
               (let uu____11804 = head_matches_delta env1 wl2 t1 t2 in
                match uu____11804 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu____11849 = eq_prob t1 t2 wl2 in
                         (match uu____11849 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11870 ->
                         let uu____11879 = eq_prob t1 t2 wl2 in
                         (match uu____11879 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu____11928 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu____11943 =
                                 FStar_Syntax_Subst.compress t11 in
                               let uu____11944 =
                                 FStar_Syntax_Subst.compress t21 in
                               (uu____11943, uu____11944)
                           | FStar_Pervasives_Native.None ->
                               let uu____11949 =
                                 FStar_Syntax_Subst.compress t1 in
                               let uu____11950 =
                                 FStar_Syntax_Subst.compress t2 in
                               (uu____11949, uu____11950) in
                         (match uu____11928 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11981 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu____11981 with
                                | (t1_hd, t1_args) ->
                                    let uu____12026 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu____12026 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12090 =
                                              let uu____12097 =
                                                let uu____12108 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu____12108 :: t1_args in
                                              let uu____12125 =
                                                let uu____12134 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu____12134 :: t2_args in
                                              FStar_List.fold_left2
                                                (fun uu____12183 ->
                                                   fun uu____12184 ->
                                                     fun uu____12185 ->
                                                       match (uu____12183,
                                                               uu____12184,
                                                               uu____12185)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu____12235),
                                                          (a2, uu____12237))
                                                           ->
                                                           let uu____12274 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu____12274
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12097
                                                uu____12125 in
                                            match uu____12090 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  let uu___1941_12300 = wl4 in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1941_12300.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1941_12300.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1941_12300.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1941_12300.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1941_12300.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____12308 =
                                                  solve env1 wl' in
                                                (match uu____12308 with
                                                 | Success
                                                     (uu____12311,
                                                      defer_to_tac, imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____12315 =
                                                         extend_wl wl4
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu____12315))
                                                 | Failed uu____12316 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu____12348 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu____12348 with
                                | (t1_base, p1_opt) ->
                                    let uu____12383 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu____12383 with
                                     | (t2_base, p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____12481 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu____12481
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
                                               let uu____12529 =
                                                 op phi11 phi21 in
                                               refine x1 uu____12529
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
                                               let uu____12559 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12559
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
                                               let uu____12589 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12589
                                           | uu____12592 -> t_base in
                                         let uu____12609 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu____12609 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____12623 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu____12623, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu____12630 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu____12630 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu____12665 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu____12665 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu____12700 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu____12700
                                                         with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu____12724 = combine t11 t21 wl2 in
                              (match uu____12724 with
                               | (t12, ps, wl3) ->
                                   ((let uu____12757 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu____12757
                                     then
                                       let uu____12758 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____12758
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu____12797 ts1 =
               match uu____12797 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12860 = pairwise out t wl2 in
                        (match uu____12860 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2)) in
             let uu____12896 =
               let uu____12907 = FStar_List.hd ts in (uu____12907, [], wl1) in
             let uu____12916 = FStar_List.tl ts in
             aux uu____12896 uu____12916 in
           let uu____12923 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu____12923 with
           | (this_flex, this_rigid) ->
               let uu____12947 =
                 let uu____12948 = FStar_Syntax_Subst.compress this_rigid in
                 uu____12948.FStar_Syntax_Syntax.n in
               (match uu____12947 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu____12973 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu____12973
                    then
                      let uu____12974 = destruct_flex_t this_flex wl in
                      (match uu____12974 with
                       | (flex, wl1) ->
                           let uu____12981 = quasi_pattern env flex in
                           (match uu____12981 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu____12999 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____12999
                                  then
                                    let uu____13000 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13000
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13003 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2051_13006 = tp in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2051_13006.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2051_13006.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2051_13006.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2051_13006.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2051_13006.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2051_13006.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2051_13006.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2051_13006.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2051_13006.FStar_TypeChecker_Common.rank)
                                }))] wl in
                       solve env uu____13003)
                | uu____13007 ->
                    ((let uu____13009 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____13009
                      then
                        let uu____13010 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13010
                      else ());
                     (let uu____13012 =
                        FStar_Syntax_Util.head_and_args this_flex in
                      match uu____13012 with
                      | (u, _args) ->
                          let uu____13055 =
                            let uu____13056 = FStar_Syntax_Subst.compress u in
                            uu____13056.FStar_Syntax_Syntax.n in
                          (match uu____13055 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu____13083 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu____13083 with
                                 | (u', uu____13101) ->
                                     let uu____13126 =
                                       let uu____13127 = whnf env u' in
                                       uu____13127.FStar_Syntax_Syntax.n in
                                     (match uu____13126 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13148 -> false) in
                               let uu____13149 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13172 ->
                                         match uu___23_13172 with
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
                                              | uu____13181 -> false)
                                         | uu____13184 -> false)) in
                               (match uu____13149 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu____13198 = whnf env this_rigid in
                                      let uu____13199 =
                                        FStar_List.collect
                                          (fun uu___24_13205 ->
                                             match uu___24_13205 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13211 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu____13211]
                                             | uu____13213 -> [])
                                          bounds_probs in
                                      uu____13198 :: uu____13199 in
                                    let uu____13214 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu____13214 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu____13245 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu____13260 =
                                               let uu____13261 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu____13261.FStar_Syntax_Syntax.n in
                                             match uu____13260 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13273 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13273)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13282 -> bound in
                                           let uu____13283 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu____13283) in
                                         (match uu____13245 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13312 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu____13312
                                                then
                                                  let wl'1 =
                                                    let uu___2111_13314 = wl1 in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2111_13314.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2111_13314.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2111_13314.ctr);
                                                      defer_ok =
                                                        (uu___2111_13314.defer_ok);
                                                      smt_ok =
                                                        (uu___2111_13314.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2111_13314.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2111_13314.tcenv);
                                                      wl_implicits =
                                                        (uu___2111_13314.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2111_13314.repr_subcomp_allowed)
                                                    } in
                                                  let uu____13315 =
                                                    wl_to_string wl'1 in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13315
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____13318 =
                                                  solve_t env eq_prob
                                                    (let uu___2116_13320 =
                                                       wl' in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2116_13320.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2116_13320.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2116_13320.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2116_13320.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2116_13320.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2116_13320.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2116_13320.repr_subcomp_allowed)
                                                     }) in
                                                match uu____13318 with
                                                | Success
                                                    (uu____13321,
                                                     defer_to_tac, imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2123_13325 =
                                                        wl' in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2123_13325.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2123_13325.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2123_13325.ctr);
                                                        defer_ok =
                                                          (uu___2123_13325.defer_ok);
                                                        smt_ok =
                                                          (uu___2123_13325.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2123_13325.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2123_13325.tcenv);
                                                        wl_implicits =
                                                          (uu___2123_13325.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2123_13325.repr_subcomp_allowed)
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
                                                    let uu____13341 =
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
                                                    ((let uu____13352 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu____13352
                                                      then
                                                        let uu____13353 =
                                                          let uu____13354 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_All.pipe_right
                                                            uu____13354
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13353
                                                      else ());
                                                     (let uu____13360 =
                                                        let uu____13375 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu____13375) in
                                                      match uu____13360 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu____13397)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13423 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13423
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
                                                                  let uu____13440
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13440))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13465 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13465
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
                                                                    let uu____13483
                                                                    =
                                                                    let uu____13488
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13488 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13483
                                                                    [] wl2 in
                                                                  let uu____13493
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13493))))
                                                      | uu____13494 ->
                                                          let uu____13509 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env
                                                            uu____13509 p)))))))
                           | uu____13512 when flip ->
                               let uu____13513 =
                                 let uu____13514 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13515 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13514 uu____13515 in
                               failwith uu____13513
                           | uu____13516 ->
                               let uu____13517 =
                                 let uu____13518 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13519 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13518 uu____13519 in
                               failwith uu____13517)))))
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
                      (fun uu____13553 ->
                         match uu____13553 with
                         | (x, i) ->
                             let uu____13572 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             (uu____13572, i)) bs_lhs in
                  let uu____13575 = lhs in
                  match uu____13575 with
                  | Flex (uu____13576, u_lhs, uu____13578) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____13675 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____13685 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu____13685, univ) in
                          match uu____13675 with
                          | (k, univ) ->
                              let uu____13692 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2 in
                              (match uu____13692 with
                               | (uu____13709, u, wl3) ->
                                   let uu____13712 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu____13712, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____13738 =
                              let uu____13751 =
                                let uu____13762 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu____13762 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_List.fold_right
                                (fun uu____13813 ->
                                   fun uu____13814 ->
                                     match (uu____13813, uu____13814) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu____13915 =
                                           let uu____13922 =
                                             let uu____13925 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13925 in
                                           copy_uvar u_lhs [] uu____13922 wl2 in
                                         (match uu____13915 with
                                          | (uu____13954, t_a, wl3) ->
                                              let uu____13957 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu____13957 with
                                               | (uu____13976, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____13751
                                ([], wl1) in
                            (match uu____13738 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_14045 ->
                                        match uu___25_14045 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____14046 -> false
                                        | uu____14049 -> true) flags in
                                 let ct' =
                                   let uu___2242_14051 = ct in
                                   let uu____14052 =
                                     let uu____14055 = FStar_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu____14055 in
                                   let uu____14070 = FStar_List.tl out_args in
                                   let uu____14087 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2242_14051.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2242_14051.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14052;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14070;
                                     FStar_Syntax_Syntax.flags = uu____14087
                                   } in
                                 ((let uu___2245_14091 = c in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2245_14091.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2245_14091.FStar_Syntax_Syntax.vars)
                                   }), wl2)) in
                      let uu____14094 =
                        FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu____14094 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14132 =
                                   imitate_comp bs bs_terms c wl1 in
                                 (match uu____14132 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu____14143 =
                                          let uu____14148 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____14148) in
                                        TERM uu____14143 in
                                      let uu____14149 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu____14149 with
                                       | (sub_prob, wl3) ->
                                           let uu____14162 =
                                             let uu____14163 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu____14163 in
                                           solve env uu____14162))
                             | (x, imp)::formals2 ->
                                 let uu____14185 =
                                   let uu____14192 =
                                     let uu____14195 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____14195
                                       FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14192 wl1 in
                                 (match uu____14185 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu____14216 =
                                          let uu____14219 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some
                                            uu____14219 in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14216 u_x in
                                      let uu____14220 =
                                        let uu____14223 =
                                          let uu____14226 =
                                            let uu____14227 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y in
                                            (uu____14227, imp) in
                                          [uu____14226] in
                                        FStar_List.append bs_terms
                                          uu____14223 in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14220 formals2 wl2) in
                           let uu____14254 = occurs_check u_lhs arrow in
                           (match uu____14254 with
                            | (uu____14265, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14276 =
                                    mklstr
                                      (fun uu____14281 ->
                                         let uu____14282 =
                                           FStar_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14282) in
                                  giveup_or_defer env orig wl uu____14276
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
              (let uu____14311 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____14311
               then
                 let uu____14312 =
                   FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu____14313 =
                   FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14312 (rel_to_string (p_rel orig)) uu____14313
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu____14438 = rhs wl1 scope env1 subst in
                     (match uu____14438 with
                      | (rhs_prob, wl2) ->
                          ((let uu____14460 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu____14460
                            then
                              let uu____14461 = prob_to_string env1 rhs_prob in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14461
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1, imp)::xs1, (hd2, imp')::ys1) when
                     let uu____14534 = FStar_Syntax_Util.eq_aqual imp imp' in
                     uu____14534 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2315_14536 = hd1 in
                       let uu____14537 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2315_14536.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2315_14536.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14537
                       } in
                     let hd21 =
                       let uu___2318_14541 = hd2 in
                       let uu____14542 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2318_14541.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2318_14541.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14542
                       } in
                     let uu____14545 =
                       let uu____14550 =
                         FStar_All.pipe_left invert_rel (p_rel orig) in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____14550
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter" in
                     (match uu____14545 with
                      | (prob, wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                          let subst1 =
                            let uu____14571 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____14571 in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                          let uu____14575 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1 in
                          (match uu____14575 with
                           | (env3, FStar_Util.Inl (sub_probs, phi), wl3) ->
                               let phi1 =
                                 let uu____14643 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____14643 in
                               ((let uu____14661 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14661
                                 then
                                   let uu____14662 =
                                     FStar_Syntax_Print.term_to_string phi1 in
                                   let uu____14663 =
                                     FStar_Syntax_Print.bv_to_string hd12 in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____14662
                                     uu____14663
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____14692 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1) in
               let uu____14725 = aux wl [] env [] bs1 bs2 in
               match uu____14725 with
               | (env1, FStar_Util.Inr msg, wl1) -> giveup_lit env1 msg orig
               | (env1, FStar_Util.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu____14778 = attempt sub_probs wl2 in
                   solve env1 uu____14778)
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
            let uu___2356_14798 = wl in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2356_14798.wl_deferred_to_tac);
              ctr = (uu___2356_14798.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2356_14798.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2356_14798.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu____14806 = try_solve env wl' in
          match uu____14806 with
          | Success (uu____14807, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____14819 = compress_tprob wl.tcenv problem in
         solve_t' env uu____14819 wl)
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
            (let uu____14826 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Rel") in
             if uu____14826
             then FStar_Util.print_string "solve_t_flex_rigid_eq\n"
             else ());
            (let uu____14828 = should_defer_flex_to_user_tac env wl lhs in
             if uu____14828
             then defer_to_user_tac env orig (flex_reason lhs) wl
             else
               (let binders_as_bv_set bs =
                  let uu____14838 =
                    FStar_List.map FStar_Pervasives_Native.fst bs in
                  FStar_Util.as_set uu____14838 FStar_Syntax_Syntax.order_bv in
                let mk_solution env1 lhs1 bs rhs1 =
                  let uu____14872 = lhs1 in
                  match uu____14872 with
                  | Flex (uu____14875, ctx_u, uu____14877) ->
                      let sol =
                        match bs with
                        | [] -> rhs1
                        | uu____14885 ->
                            let uu____14886 = sn_binders env1 bs in
                            u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                              uu____14886 rhs1 in
                      [TERM (ctx_u, sol)] in
                let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                  (let uu____14934 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu____14934
                   then FStar_Util.print_string "try_quasi_pattern\n"
                   else ());
                  (let uu____14936 = quasi_pattern env1 lhs1 in
                   match uu____14936 with
                   | FStar_Pervasives_Native.None ->
                       ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                   | FStar_Pervasives_Native.Some (bs, uu____14966) ->
                       let uu____14971 = lhs1 in
                       (match uu____14971 with
                        | Flex (t_lhs, ctx_u, args) ->
                            let uu____14985 = occurs_check ctx_u rhs1 in
                            (match uu____14985 with
                             | (uvars, occurs_ok, msg) ->
                                 if Prims.op_Negation occurs_ok
                                 then
                                   let uu____15027 =
                                     let uu____15034 =
                                       let uu____15035 = FStar_Option.get msg in
                                       Prims.op_Hat
                                         "quasi-pattern, occurs-check failed: "
                                         uu____15035 in
                                     FStar_Util.Inl uu____15034 in
                                   (uu____15027, wl1)
                                 else
                                   (let fvs_lhs =
                                      binders_as_bv_set
                                        (FStar_List.append
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                           bs) in
                                    let fvs_rhs =
                                      FStar_Syntax_Free.names rhs1 in
                                    let uu____15057 =
                                      let uu____15058 =
                                        FStar_Util.set_is_subset_of fvs_rhs
                                          fvs_lhs in
                                      Prims.op_Negation uu____15058 in
                                    if uu____15057
                                    then
                                      ((FStar_Util.Inl
                                          "quasi-pattern, free names on the RHS are not included in the LHS"),
                                        wl1)
                                    else
                                      (let uu____15078 =
                                         let uu____15085 =
                                           mk_solution env1 lhs1 bs rhs1 in
                                         FStar_Util.Inr uu____15085 in
                                       let uu____15090 =
                                         restrict_all_uvars env1 ctx_u []
                                           uvars wl1 in
                                       (uu____15078, uu____15090)))))) in
                let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                  let uu____15139 = FStar_Syntax_Util.head_and_args rhs1 in
                  match uu____15139 with
                  | (rhs_hd, args) ->
                      let uu____15182 = FStar_Util.prefix args in
                      (match uu____15182 with
                       | (args_rhs, last_arg_rhs) ->
                           let rhs' =
                             FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                               rhs1.FStar_Syntax_Syntax.pos in
                           let uu____15252 = lhs1 in
                           (match uu____15252 with
                            | Flex (t_lhs, u_lhs, _lhs_args) ->
                                let uu____15256 =
                                  let uu____15267 =
                                    let uu____15274 =
                                      let uu____15277 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_left
                                        FStar_Pervasives_Native.fst
                                        uu____15277 in
                                    copy_uvar u_lhs [] uu____15274 wl1 in
                                  match uu____15267 with
                                  | (uu____15304, t_last_arg, wl2) ->
                                      let uu____15307 =
                                        let b =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg in
                                        let uu____15315 =
                                          let uu____15318 =
                                            let uu____15321 =
                                              let uu____15324 =
                                                FStar_All.pipe_right
                                                  t_res_lhs
                                                  (env1.FStar_TypeChecker_Env.universe_of
                                                     env1) in
                                              FStar_All.pipe_right
                                                uu____15324
                                                (fun uu____15327 ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____15327) in
                                            FStar_All.pipe_right uu____15321
                                              (FStar_Syntax_Syntax.mk_Total'
                                                 t_res_lhs) in
                                          FStar_All.pipe_right uu____15318
                                            (FStar_Syntax_Util.arrow [b]) in
                                        copy_uvar u_lhs
                                          (FStar_List.append bs_lhs [b])
                                          uu____15315 wl2 in
                                      (match uu____15307 with
                                       | (uu____15376, lhs', wl3) ->
                                           let uu____15379 =
                                             copy_uvar u_lhs bs_lhs
                                               t_last_arg wl3 in
                                           (match uu____15379 with
                                            | (uu____15396, lhs'_last_arg,
                                               wl4) ->
                                                (lhs', lhs'_last_arg, wl4))) in
                                (match uu____15256 with
                                 | (lhs', lhs'_last_arg, wl2) ->
                                     let sol =
                                       let uu____15417 =
                                         let uu____15418 =
                                           let uu____15423 =
                                             let uu____15424 =
                                               let uu____15427 =
                                                 let uu____15428 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lhs'_last_arg in
                                                 [uu____15428] in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 lhs' uu____15427
                                                 t_lhs.FStar_Syntax_Syntax.pos in
                                             FStar_Syntax_Util.abs bs_lhs
                                               uu____15424
                                               (FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Util.residual_tot
                                                     t_res_lhs)) in
                                           (u_lhs, uu____15423) in
                                         TERM uu____15418 in
                                       [uu____15417] in
                                     let uu____15453 =
                                       let uu____15460 =
                                         mk_t_problem wl2 [] orig1 lhs'
                                           FStar_TypeChecker_Common.EQ rhs'
                                           FStar_Pervasives_Native.None
                                           "first-order lhs" in
                                       match uu____15460 with
                                       | (p1, wl3) ->
                                           let uu____15479 =
                                             mk_t_problem wl3 [] orig1
                                               lhs'_last_arg
                                               FStar_TypeChecker_Common.EQ
                                               (FStar_Pervasives_Native.fst
                                                  last_arg_rhs)
                                               FStar_Pervasives_Native.None
                                               "first-order rhs" in
                                           (match uu____15479 with
                                            | (p2, wl4) -> ([p1; p2], wl4)) in
                                     (match uu____15453 with
                                      | (sub_probs, wl3) ->
                                          let uu____15510 =
                                            let uu____15511 =
                                              solve_prob orig1
                                                FStar_Pervasives_Native.None
                                                sol wl3 in
                                            attempt sub_probs uu____15511 in
                                          solve env1 uu____15510)))) in
                let first_order orig1 env1 wl1 lhs1 rhs1 =
                  (let uu____15539 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu____15539
                   then FStar_Util.print_string "first_order\n"
                   else ());
                  (let is_app rhs2 =
                     let uu____15547 = FStar_Syntax_Util.head_and_args rhs2 in
                     match uu____15547 with
                     | (uu____15564, args) ->
                         (match args with | [] -> false | uu____15598 -> true) in
                   let is_arrow rhs2 =
                     let uu____15615 =
                       let uu____15616 = FStar_Syntax_Subst.compress rhs2 in
                       uu____15616.FStar_Syntax_Syntax.n in
                     match uu____15615 with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15619 -> true
                     | uu____15634 -> false in
                   let uu____15635 = quasi_pattern env1 lhs1 in
                   match uu____15635 with
                   | FStar_Pervasives_Native.None ->
                       let msg =
                         mklstr
                           (fun uu____15653 ->
                              let uu____15654 = prob_to_string env1 orig1 in
                              FStar_Util.format1
                                "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                                uu____15654) in
                       giveup_or_defer env1 orig1 wl1 msg
                   | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                       let uu____15661 = is_app rhs1 in
                       if uu____15661
                       then
                         imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                           rhs1
                       else
                         (let uu____15663 = is_arrow rhs1 in
                          if uu____15663
                          then
                            imitate_arrow orig1 env1 wl1 lhs1 bs_lhs
                              t_res_lhs FStar_TypeChecker_Common.EQ rhs1
                          else
                            (let msg =
                               mklstr
                                 (fun uu____15672 ->
                                    let uu____15673 =
                                      prob_to_string env1 orig1 in
                                    FStar_Util.format1
                                      "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                      uu____15673) in
                             giveup_or_defer env1 orig1 wl1 msg))) in
                match p_rel orig with
                | FStar_TypeChecker_Common.SUB ->
                    if wl.defer_ok
                    then
                      let uu____15674 =
                        FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl uu____15674
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.SUBINV ->
                    if wl.defer_ok
                    then
                      let uu____15676 =
                        FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl uu____15676
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.EQ ->
                    let uu____15678 = lhs in
                    (match uu____15678 with
                     | Flex (_t1, ctx_uv, args_lhs) ->
                         let uu____15682 =
                           pat_vars env
                             ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                             args_lhs in
                         (match uu____15682 with
                          | FStar_Pervasives_Native.Some lhs_binders ->
                              ((let uu____15689 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel") in
                                if uu____15689
                                then
                                  FStar_Util.print_string "it's a pattern\n"
                                else ());
                               (let rhs1 = sn env rhs in
                                let names_to_string1 fvs =
                                  let uu____15702 =
                                    let uu____15705 =
                                      FStar_Util.set_elements fvs in
                                    FStar_List.map
                                      FStar_Syntax_Print.bv_to_string
                                      uu____15705 in
                                  FStar_All.pipe_right uu____15702
                                    (FStar_String.concat ", ") in
                                let fvs1 =
                                  binders_as_bv_set
                                    (FStar_List.append
                                       ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                       lhs_binders) in
                                let fvs2 = FStar_Syntax_Free.names rhs1 in
                                let uu____15722 = occurs_check ctx_uv rhs1 in
                                match uu____15722 with
                                | (uvars, occurs_ok, msg) ->
                                    if Prims.op_Negation occurs_ok
                                    then
                                      let uu____15744 =
                                        let uu____15745 =
                                          let uu____15746 =
                                            FStar_Option.get msg in
                                          Prims.op_Hat
                                            "occurs-check failed: "
                                            uu____15746 in
                                        FStar_All.pipe_left FStar_Thunk.mkv
                                          uu____15745 in
                                      giveup_or_defer env orig wl uu____15744
                                    else
                                      (let uu____15748 =
                                         FStar_Util.set_is_subset_of fvs2
                                           fvs1 in
                                       if uu____15748
                                       then
                                         let sol =
                                           mk_solution env lhs lhs_binders
                                             rhs1 in
                                         let wl1 =
                                           restrict_all_uvars env ctx_uv
                                             lhs_binders uvars wl in
                                         let uu____15753 =
                                           solve_prob orig
                                             FStar_Pervasives_Native.None sol
                                             wl1 in
                                         solve env uu____15753
                                       else
                                         if wl.defer_ok
                                         then
                                           (let msg1 =
                                              mklstr
                                                (fun uu____15766 ->
                                                   let uu____15767 =
                                                     names_to_string1 fvs2 in
                                                   let uu____15768 =
                                                     names_to_string1 fvs1 in
                                                   let uu____15769 =
                                                     FStar_Syntax_Print.binders_to_string
                                                       ", "
                                                       (FStar_List.append
                                                          ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                          lhs_binders) in
                                                   FStar_Util.format3
                                                     "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                     uu____15767 uu____15768
                                                     uu____15769) in
                                            giveup_or_defer env orig wl msg1)
                                         else
                                           first_order orig env wl lhs rhs1)))
                          | uu____15777 ->
                              if wl.defer_ok
                              then
                                let uu____15780 =
                                  FStar_Thunk.mkv "Not a pattern" in
                                giveup_or_defer env orig wl uu____15780
                              else
                                (let uu____15782 =
                                   try_quasi_pattern orig env wl lhs rhs in
                                 match uu____15782 with
                                 | (FStar_Util.Inr sol, wl1) ->
                                     let uu____15805 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None sol wl1 in
                                     solve env uu____15805
                                 | (FStar_Util.Inl msg, uu____15807) ->
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
                  let uu____15821 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15821
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok
                then
                  let uu____15823 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15823
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu____15825 =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu____15825
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
                    (let uu____15827 =
                       FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer env orig wl uu____15827)
                  else
                    (let uu____15829 =
                       let uu____15846 = quasi_pattern env lhs in
                       let uu____15853 = quasi_pattern env rhs in
                       (uu____15846, uu____15853) in
                     match uu____15829 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs, t_res_lhs),
                        FStar_Pervasives_Native.Some
                        (binders_rhs, t_res_rhs)) ->
                         let uu____15896 = lhs in
                         (match uu____15896 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____15897;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____15899;_},
                               u_lhs, uu____15901)
                              ->
                              let uu____15904 = rhs in
                              (match uu____15904 with
                               | Flex (uu____15905, u_rhs, uu____15907) ->
                                   let uu____15908 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs) in
                                   if uu____15908
                                   then
                                     let uu____15913 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl in
                                     solve env uu____15913
                                   else
                                     (let uu____15915 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                      match uu____15915 with
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
                                          let uu____15947 =
                                            let uu____15954 =
                                              let uu____15957 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs in
                                              FStar_Syntax_Util.arrow zs
                                                uu____15957 in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____15954
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
                                          (match uu____15947 with
                                           | (uu____15961, w, wl1) ->
                                               let w_app =
                                                 let uu____15965 =
                                                   FStar_List.map
                                                     (fun uu____15976 ->
                                                        match uu____15976
                                                        with
                                                        | (z, uu____15984) ->
                                                            let uu____15989 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____15989) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____15965
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____15991 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____15991
                                                 then
                                                   let uu____15992 =
                                                     let uu____15995 =
                                                       flex_t_to_string lhs in
                                                     let uu____15996 =
                                                       let uu____15999 =
                                                         flex_t_to_string rhs in
                                                       let uu____16000 =
                                                         let uu____16003 =
                                                           term_to_string w in
                                                         let uu____16004 =
                                                           let uu____16007 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____16014 =
                                                             let uu____16017
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____16024
                                                               =
                                                               let uu____16027
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____16027] in
                                                             uu____16017 ::
                                                               uu____16024 in
                                                           uu____16007 ::
                                                             uu____16014 in
                                                         uu____16003 ::
                                                           uu____16004 in
                                                       uu____15999 ::
                                                         uu____16000 in
                                                     uu____15995 ::
                                                       uu____15996 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____15992
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____16033 =
                                                       let uu____16038 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____16038) in
                                                     TERM uu____16033 in
                                                   let uu____16039 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____16039
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____16044 =
                                                          let uu____16049 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____16049) in
                                                        TERM uu____16044 in
                                                      [s1; s2]) in
                                                 let uu____16050 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____16050))))))
                     | uu____16051 ->
                         let uu____16068 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____16068)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____16117 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____16117
            then
              let uu____16118 = FStar_Syntax_Print.term_to_string t1 in
              let uu____16119 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____16120 = FStar_Syntax_Print.term_to_string t2 in
              let uu____16121 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16118 uu____16119 uu____16120 uu____16121
            else ());
           (let uu____16124 = FStar_Syntax_Util.head_and_args t1 in
            match uu____16124 with
            | (head1, args1) ->
                let uu____16167 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____16167 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16232 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____16232 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____16236 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____16236) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16254 =
                         mklstr
                           (fun uu____16265 ->
                              let uu____16266 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____16267 = args_to_string args1 in
                              let uu____16270 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____16271 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____16266 uu____16267 uu____16270
                                uu____16271) in
                       giveup env1 uu____16254 orig
                     else
                       (let uu____16275 =
                          (nargs = Prims.int_zero) ||
                            (let uu____16277 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____16277 = FStar_Syntax_Util.Equal) in
                        if uu____16275
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2638_16279 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2638_16279.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2638_16279.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2638_16279.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2638_16279.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2638_16279.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2638_16279.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2638_16279.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2638_16279.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____16286 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____16286
                                    else solve env1 wl2))
                        else
                          (let uu____16289 = base_and_refinement env1 t1 in
                           match uu____16289 with
                           | (base1, refinement1) ->
                               let uu____16314 = base_and_refinement env1 t2 in
                               (match uu____16314 with
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
                                           let uu____16477 =
                                             FStar_List.fold_right
                                               (fun uu____16517 ->
                                                  fun uu____16518 ->
                                                    match (uu____16517,
                                                            uu____16518)
                                                    with
                                                    | (((a1, uu____16570),
                                                        (a2, uu____16572)),
                                                       (probs, wl3)) ->
                                                        let uu____16621 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____16621
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____16477 with
                                           | (subprobs, wl3) ->
                                               ((let uu____16663 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16663
                                                 then
                                                   let uu____16664 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____16664
                                                 else ());
                                                (let uu____16667 =
                                                   FStar_Options.defensive () in
                                                 if uu____16667
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
                                                    (let uu____16687 =
                                                       mk_sub_probs wl3 in
                                                     match uu____16687 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____16703 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____16703 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____16711 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____16711)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____16735 =
                                                    mk_sub_probs wl3 in
                                                  match uu____16735 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____16751 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____16751 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____16759 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____16759) in
                                         let unfold_and_retry d env2 wl2
                                           uu____16786 =
                                           match uu____16786 with
                                           | (prob, reason) ->
                                               ((let uu____16800 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16800
                                                 then
                                                   let uu____16801 =
                                                     prob_to_string env2 orig in
                                                   let uu____16802 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____16801 uu____16802
                                                 else ());
                                                (let uu____16804 =
                                                   let uu____16813 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____16816 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____16813, uu____16816) in
                                                 match uu____16804 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____16829 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____16829 with
                                                      | (head1', uu____16847)
                                                          ->
                                                          let uu____16872 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____16872
                                                           with
                                                           | (head2',
                                                              uu____16890) ->
                                                               let uu____16915
                                                                 =
                                                                 let uu____16920
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____16921
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____16920,
                                                                   uu____16921) in
                                                               (match uu____16915
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu____16923
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____16923
                                                                    then
                                                                    let uu____16924
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____16925
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____16926
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____16927
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____16924
                                                                    uu____16925
                                                                    uu____16926
                                                                    uu____16927
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____16929
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2726_16937
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2726_16937.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2726_16937.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2726_16937.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2726_16937.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2726_16937.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2726_16937.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2726_16937.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2726_16937.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
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
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____16940
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____16942 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____16954 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____16954 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____16961 =
                                             let uu____16962 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____16962.FStar_Syntax_Syntax.n in
                                           match uu____16961 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____16966 -> false in
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
                                          | uu____16968 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____16971 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2746_17007 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2746_17007.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2746_17007.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2746_17007.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2746_17007.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2746_17007.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2746_17007.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2746_17007.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2746_17007.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17082 = destruct_flex_t scrutinee wl1 in
             match uu____17082 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____17093 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____17093 with
                  | (xs, pat_term, uu____17108, uu____17109) ->
                      let uu____17114 =
                        FStar_List.fold_left
                          (fun uu____17137 ->
                             fun x ->
                               match uu____17137 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____17158 = copy_uvar uv [] t_x wl3 in
                                   (match uu____17158 with
                                    | (uu____17177, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____17114 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____17198 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____17198 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2787_17214 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2787_17214.wl_deferred_to_tac);
                                    ctr = (uu___2787_17214.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2787_17214.umax_heuristic_ok);
                                    tcenv = (uu___2787_17214.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2787_17214.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____17222 = solve env1 wl' in
                                (match uu____17222 with
                                 | Success (uu____17225, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2796_17229 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2796_17229.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2796_17229.wl_deferred_to_tac);
                                         ctr = (uu___2796_17229.ctr);
                                         defer_ok =
                                           (uu___2796_17229.defer_ok);
                                         smt_ok = (uu___2796_17229.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2796_17229.umax_heuristic_ok);
                                         tcenv = (uu___2796_17229.tcenv);
                                         wl_implicits =
                                           (uu___2796_17229.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2796_17229.repr_subcomp_allowed)
                                       } in
                                     let uu____17230 = solve env1 wl'1 in
                                     (match uu____17230 with
                                      | Success
                                          (uu____17233, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____17237 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____17237))
                                      | Failed uu____17242 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17248 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____17269 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____17269
                 then
                   let uu____17270 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____17271 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17270 uu____17271
                 else ());
                (let uu____17273 =
                   let uu____17294 =
                     let uu____17303 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____17303) in
                   let uu____17310 =
                     let uu____17319 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____17319) in
                   (uu____17294, uu____17310) in
                 match uu____17273 with
                 | ((uu____17348,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____17351;
                       FStar_Syntax_Syntax.vars = uu____17352;_}),
                    (s, t)) ->
                     let uu____17423 =
                       let uu____17424 = is_flex scrutinee in
                       Prims.op_Negation uu____17424 in
                     if uu____17423
                     then
                       ((let uu____17432 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____17432
                         then
                           let uu____17433 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17433
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17445 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17445
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17451 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17451
                           then
                             let uu____17452 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____17453 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17452 uu____17453
                           else ());
                          (let pat_discriminates uu___26_17474 =
                             match uu___26_17474 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17489;
                                  FStar_Syntax_Syntax.p = uu____17490;_},
                                FStar_Pervasives_Native.None, uu____17491) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17504;
                                  FStar_Syntax_Syntax.p = uu____17505;_},
                                FStar_Pervasives_Native.None, uu____17506) ->
                                 true
                             | uu____17531 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____17631 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____17631 with
                                       | (uu____17632, uu____17633, t') ->
                                           let uu____17651 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____17651 with
                                            | (FullMatch, uu____17662) ->
                                                true
                                            | (HeadMatch uu____17675,
                                               uu____17676) -> true
                                            | uu____17689 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____17722 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____17722
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17727 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____17727 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____17815, uu____17816)
                                       -> branches1
                                   | uu____17961 -> branches in
                                 let uu____18016 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____18025 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____18025 with
                                        | (p, uu____18029, uu____18030) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____18057 ->
                                      FStar_Util.Inr uu____18057) uu____18016))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18087 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____18087 with
                                | (p, uu____18095, e) ->
                                    ((let uu____18114 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____18114
                                      then
                                        let uu____18115 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____18116 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18115 uu____18116
                                      else ());
                                     (let uu____18118 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____18131 ->
                                           FStar_Util.Inr uu____18131)
                                        uu____18118)))))
                 | ((s, t),
                    (uu____18134,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____18137;
                       FStar_Syntax_Syntax.vars = uu____18138;_}))
                     ->
                     let uu____18207 =
                       let uu____18208 = is_flex scrutinee in
                       Prims.op_Negation uu____18208 in
                     if uu____18207
                     then
                       ((let uu____18216 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____18216
                         then
                           let uu____18217 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18217
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18229 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18229
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18235 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18235
                           then
                             let uu____18236 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____18237 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18236 uu____18237
                           else ());
                          (let pat_discriminates uu___26_18258 =
                             match uu___26_18258 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18273;
                                  FStar_Syntax_Syntax.p = uu____18274;_},
                                FStar_Pervasives_Native.None, uu____18275) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18288;
                                  FStar_Syntax_Syntax.p = uu____18289;_},
                                FStar_Pervasives_Native.None, uu____18290) ->
                                 true
                             | uu____18315 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____18415 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____18415 with
                                       | (uu____18416, uu____18417, t') ->
                                           let uu____18435 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____18435 with
                                            | (FullMatch, uu____18446) ->
                                                true
                                            | (HeadMatch uu____18459,
                                               uu____18460) -> true
                                            | uu____18473 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____18506 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____18506
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18511 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____18511 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____18599, uu____18600)
                                       -> branches1
                                   | uu____18745 -> branches in
                                 let uu____18800 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____18809 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____18809 with
                                        | (p, uu____18813, uu____18814) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____18841 ->
                                      FStar_Util.Inr uu____18841) uu____18800))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18871 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____18871 with
                                | (p, uu____18879, e) ->
                                    ((let uu____18898 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____18898
                                      then
                                        let uu____18899 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____18900 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18899 uu____18900
                                      else ());
                                     (let uu____18902 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____18915 ->
                                           FStar_Util.Inr uu____18915)
                                        uu____18902)))))
                 | uu____18916 ->
                     ((let uu____18938 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____18938
                       then
                         let uu____18939 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____18940 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____18939 uu____18940
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____18982 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____18982
            then
              let uu____18983 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____18984 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____18985 = FStar_Syntax_Print.term_to_string t1 in
              let uu____18986 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____18983 uu____18984 uu____18985 uu____18986
            else ());
           (let uu____18988 = head_matches_delta env1 wl1 t1 t2 in
            match uu____18988 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____19019, uu____19020) ->
                     let rec may_relate head =
                       let uu____19047 =
                         let uu____19048 = FStar_Syntax_Subst.compress head in
                         uu____19048.FStar_Syntax_Syntax.n in
                       match uu____19047 with
                       | FStar_Syntax_Syntax.Tm_name uu____19051 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____19052 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____19076 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____19076 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____19077 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____19078
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____19079 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____19081, uu____19082) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____19124) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____19130) ->
                           may_relate t
                       | uu____19135 -> false in
                     let uu____19136 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____19136 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____19146 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____19146
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____19152 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____19152
                          then
                            let uu____19153 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____19153 with
                             | (guard, wl2) ->
                                 let uu____19160 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____19160)
                          else
                            (let uu____19162 =
                               mklstr
                                 (fun uu____19173 ->
                                    let uu____19174 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____19175 =
                                      let uu____19176 =
                                        let uu____19179 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____19179
                                          (fun x ->
                                             let uu____19185 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____19185) in
                                      FStar_Util.dflt "" uu____19176 in
                                    let uu____19186 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____19187 =
                                      let uu____19188 =
                                        let uu____19191 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____19191
                                          (fun x ->
                                             let uu____19197 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____19197) in
                                      FStar_Util.dflt "" uu____19188 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____19174 uu____19175 uu____19186
                                      uu____19187) in
                             giveup env1 uu____19162 orig))
                 | (HeadMatch (true), uu____19198) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____19211 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____19211 with
                        | (guard, wl2) ->
                            let uu____19218 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____19218)
                     else
                       (let uu____19220 =
                          mklstr
                            (fun uu____19227 ->
                               let uu____19228 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____19229 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____19228 uu____19229) in
                        giveup env1 uu____19220 orig)
                 | (uu____19230, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2978_19244 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2978_19244.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2978_19244.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2978_19244.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2978_19244.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2978_19244.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2978_19244.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2978_19244.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2978_19244.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____19268 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____19268
          then
            let uu____19269 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____19269
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____19274 =
                let uu____19277 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19277 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____19274 t1);
             (let uu____19295 =
                let uu____19298 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19298 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____19295 t2);
             (let uu____19316 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____19316
              then
                let uu____19317 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____19318 =
                  let uu____19319 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____19320 =
                    let uu____19321 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____19321 in
                  Prims.op_Hat uu____19319 uu____19320 in
                let uu____19322 =
                  let uu____19323 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____19324 =
                    let uu____19325 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____19325 in
                  Prims.op_Hat uu____19323 uu____19324 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____19317 uu____19318 uu____19322
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____19328, uu____19329) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____19344, FStar_Syntax_Syntax.Tm_delayed uu____19345) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____19360, uu____19361) ->
                  let uu____19388 =
                    let uu___3009_19389 = problem in
                    let uu____19390 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3009_19389.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19390;
                      FStar_TypeChecker_Common.relation =
                        (uu___3009_19389.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3009_19389.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3009_19389.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3009_19389.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3009_19389.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3009_19389.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3009_19389.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3009_19389.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19388 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____19391, uu____19392) ->
                  let uu____19399 =
                    let uu___3015_19400 = problem in
                    let uu____19401 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3015_19400.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19401;
                      FStar_TypeChecker_Common.relation =
                        (uu___3015_19400.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3015_19400.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3015_19400.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3015_19400.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3015_19400.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3015_19400.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3015_19400.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3015_19400.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19399 wl
              | (uu____19402, FStar_Syntax_Syntax.Tm_ascribed uu____19403) ->
                  let uu____19430 =
                    let uu___3021_19431 = problem in
                    let uu____19432 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3021_19431.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3021_19431.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3021_19431.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19432;
                      FStar_TypeChecker_Common.element =
                        (uu___3021_19431.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3021_19431.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3021_19431.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3021_19431.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3021_19431.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3021_19431.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19430 wl
              | (uu____19433, FStar_Syntax_Syntax.Tm_meta uu____19434) ->
                  let uu____19441 =
                    let uu___3027_19442 = problem in
                    let uu____19443 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3027_19442.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3027_19442.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3027_19442.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19443;
                      FStar_TypeChecker_Common.element =
                        (uu___3027_19442.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3027_19442.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3027_19442.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3027_19442.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3027_19442.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3027_19442.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19441 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____19445),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____19447)) ->
                  let uu____19456 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____19456
              | (FStar_Syntax_Syntax.Tm_bvar uu____19457, uu____19458) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____19459, FStar_Syntax_Syntax.Tm_bvar uu____19460) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_19529 =
                    match uu___27_19529 with
                    | [] -> c
                    | bs ->
                        let uu____19557 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____19557 in
                  let uu____19568 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____19568 with
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
                                    let uu____19717 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____19717
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_19802 =
                    match uu___28_19802 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____19844 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____19844 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____19989 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____19990 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____19989
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____19990 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____19991, uu____19992) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20021 -> true
                    | uu____20040 -> false in
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
                      (let uu____20093 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3129_20101 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3129_20101.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3129_20101.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3129_20101.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3129_20101.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3129_20101.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3129_20101.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3129_20101.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3129_20101.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3129_20101.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3129_20101.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3129_20101.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3129_20101.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3129_20101.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3129_20101.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3129_20101.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3129_20101.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3129_20101.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3129_20101.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3129_20101.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3129_20101.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3129_20101.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3129_20101.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3129_20101.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3129_20101.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3129_20101.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3129_20101.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3129_20101.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3129_20101.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3129_20101.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3129_20101.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3129_20101.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3129_20101.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3129_20101.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3129_20101.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3129_20101.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3129_20101.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3129_20101.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3129_20101.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3129_20101.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3129_20101.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3129_20101.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3129_20101.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3129_20101.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3129_20101.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____20093 with
                       | (uu____20104, ty, uu____20106) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____20115 =
                                 let uu____20116 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____20116.FStar_Syntax_Syntax.n in
                               match uu____20115 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20119 ->
                                   let uu____20126 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____20126
                               | uu____20127 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____20130 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____20130
                             then
                               let uu____20131 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____20132 =
                                 let uu____20133 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20133 in
                               let uu____20134 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20131 uu____20132 uu____20134
                             else ());
                            r1)) in
                  let uu____20136 =
                    let uu____20153 = maybe_eta t1 in
                    let uu____20160 = maybe_eta t2 in
                    (uu____20153, uu____20160) in
                  (match uu____20136 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3150_20202 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3150_20202.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3150_20202.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3150_20202.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3150_20202.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3150_20202.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3150_20202.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3150_20202.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3150_20202.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20223 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20223
                       then
                         let uu____20224 = destruct_flex_t not_abs wl in
                         (match uu____20224 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3167_20239 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3167_20239.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3167_20239.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3167_20239.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3167_20239.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3167_20239.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3167_20239.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3167_20239.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3167_20239.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20241 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20241 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20262 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20262
                       then
                         let uu____20263 = destruct_flex_t not_abs wl in
                         (match uu____20263 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3167_20278 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3167_20278.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3167_20278.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3167_20278.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3167_20278.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3167_20278.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3167_20278.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3167_20278.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3167_20278.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20280 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20280 orig))
                   | uu____20281 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____20298, FStar_Syntax_Syntax.Tm_abs uu____20299) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20328 -> true
                    | uu____20347 -> false in
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
                      (let uu____20400 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3129_20408 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3129_20408.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3129_20408.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3129_20408.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3129_20408.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3129_20408.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3129_20408.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3129_20408.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3129_20408.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3129_20408.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3129_20408.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3129_20408.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3129_20408.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3129_20408.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3129_20408.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3129_20408.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3129_20408.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3129_20408.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3129_20408.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3129_20408.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3129_20408.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3129_20408.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3129_20408.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3129_20408.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3129_20408.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3129_20408.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3129_20408.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3129_20408.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3129_20408.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3129_20408.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3129_20408.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3129_20408.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3129_20408.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3129_20408.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3129_20408.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3129_20408.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3129_20408.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3129_20408.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3129_20408.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3129_20408.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3129_20408.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3129_20408.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3129_20408.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3129_20408.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3129_20408.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____20400 with
                       | (uu____20411, ty, uu____20413) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____20422 =
                                 let uu____20423 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____20423.FStar_Syntax_Syntax.n in
                               match uu____20422 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20426 ->
                                   let uu____20433 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____20433
                               | uu____20434 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____20437 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____20437
                             then
                               let uu____20438 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____20439 =
                                 let uu____20440 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20440 in
                               let uu____20441 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20438 uu____20439 uu____20441
                             else ());
                            r1)) in
                  let uu____20443 =
                    let uu____20460 = maybe_eta t1 in
                    let uu____20467 = maybe_eta t2 in
                    (uu____20460, uu____20467) in
                  (match uu____20443 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3150_20509 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3150_20509.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3150_20509.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3150_20509.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3150_20509.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3150_20509.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3150_20509.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3150_20509.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3150_20509.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20530 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20530
                       then
                         let uu____20531 = destruct_flex_t not_abs wl in
                         (match uu____20531 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3167_20546 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3167_20546.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3167_20546.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3167_20546.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3167_20546.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3167_20546.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3167_20546.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3167_20546.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3167_20546.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20548 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20548 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20569 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20569
                       then
                         let uu____20570 = destruct_flex_t not_abs wl in
                         (match uu____20570 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3167_20585 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3167_20585.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3167_20585.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3167_20585.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3167_20585.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3167_20585.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3167_20585.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3167_20585.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3167_20585.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20587 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20587 orig))
                   | uu____20588 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____20617 =
                    let uu____20622 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____20622 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3190_20650 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3190_20650.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3190_20650.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3192_20652 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3192_20652.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3192_20652.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____20653, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3190_20667 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3190_20667.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3190_20667.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3192_20669 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3192_20669.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3192_20669.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____20670 -> (x1, x2) in
                  (match uu____20617 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____20689 = as_refinement false env t11 in
                       (match uu____20689 with
                        | (x12, phi11) ->
                            let uu____20696 = as_refinement false env t21 in
                            (match uu____20696 with
                             | (x22, phi21) ->
                                 ((let uu____20704 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____20704
                                   then
                                     ((let uu____20706 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____20707 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____20708 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____20706
                                         uu____20707 uu____20708);
                                      (let uu____20709 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____20710 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____20711 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____20709
                                         uu____20710 uu____20711))
                                   else ());
                                  (let uu____20713 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____20713 with
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
                                         let uu____20781 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____20781
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____20793 =
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
                                         (let uu____20804 =
                                            let uu____20807 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20807 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____20804
                                            (p_guard base_prob));
                                         (let uu____20825 =
                                            let uu____20828 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20828 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____20825
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____20846 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____20846) in
                                       let has_uvars =
                                         (let uu____20850 =
                                            let uu____20851 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____20851 in
                                          Prims.op_Negation uu____20850) ||
                                           (let uu____20855 =
                                              let uu____20856 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____20856 in
                                            Prims.op_Negation uu____20855) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____20859 =
                                           let uu____20864 =
                                             let uu____20873 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____20873] in
                                           mk_t_problem wl1 uu____20864 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____20859 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____20895 =
                                                solve env1
                                                  (let uu___3235_20897 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3235_20897.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3235_20897.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3235_20897.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3235_20897.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3235_20897.tcenv);
                                                     wl_implicits =
                                                       (uu___3235_20897.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3235_20897.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____20895 with
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
                                                   (uu____20908,
                                                    defer_to_tac,
                                                    uu____20910)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____20915 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____20915 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3251_20924 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3251_20924.attempting);
                                                         wl_deferred =
                                                           (uu___3251_20924.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3251_20924.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3251_20924.defer_ok);
                                                         smt_ok =
                                                           (uu___3251_20924.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3251_20924.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3251_20924.tcenv);
                                                         wl_implicits =
                                                           (uu___3251_20924.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3251_20924.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____20926 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____20926))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20928,
                 FStar_Syntax_Syntax.Tm_uvar uu____20929) ->
                  let uu____20954 = ensure_no_uvar_subst t1 wl in
                  (match uu____20954 with
                   | (t11, wl1) ->
                       let uu____20961 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20961 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20970;
                    FStar_Syntax_Syntax.pos = uu____20971;
                    FStar_Syntax_Syntax.vars = uu____20972;_},
                  uu____20973),
                 FStar_Syntax_Syntax.Tm_uvar uu____20974) ->
                  let uu____21023 = ensure_no_uvar_subst t1 wl in
                  (match uu____21023 with
                   | (t11, wl1) ->
                       let uu____21030 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21030 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____21039,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21040;
                    FStar_Syntax_Syntax.pos = uu____21041;
                    FStar_Syntax_Syntax.vars = uu____21042;_},
                  uu____21043)) ->
                  let uu____21092 = ensure_no_uvar_subst t1 wl in
                  (match uu____21092 with
                   | (t11, wl1) ->
                       let uu____21099 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21099 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21108;
                    FStar_Syntax_Syntax.pos = uu____21109;
                    FStar_Syntax_Syntax.vars = uu____21110;_},
                  uu____21111),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21112;
                    FStar_Syntax_Syntax.pos = uu____21113;
                    FStar_Syntax_Syntax.vars = uu____21114;_},
                  uu____21115)) ->
                  let uu____21188 = ensure_no_uvar_subst t1 wl in
                  (match uu____21188 with
                   | (t11, wl1) ->
                       let uu____21195 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21195 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____21204, uu____21205) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21218 = destruct_flex_t t1 wl in
                  (match uu____21218 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21225;
                    FStar_Syntax_Syntax.pos = uu____21226;
                    FStar_Syntax_Syntax.vars = uu____21227;_},
                  uu____21228),
                 uu____21229) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21266 = destruct_flex_t t1 wl in
                  (match uu____21266 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____21273, FStar_Syntax_Syntax.Tm_uvar uu____21274) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____21287, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21288;
                    FStar_Syntax_Syntax.pos = uu____21289;
                    FStar_Syntax_Syntax.vars = uu____21290;_},
                  uu____21291)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____21328,
                 FStar_Syntax_Syntax.Tm_arrow uu____21329) ->
                  solve_t' env
                    (let uu___3354_21357 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3354_21357.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3354_21357.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3354_21357.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3354_21357.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3354_21357.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3354_21357.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3354_21357.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3354_21357.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3354_21357.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21358;
                    FStar_Syntax_Syntax.pos = uu____21359;
                    FStar_Syntax_Syntax.vars = uu____21360;_},
                  uu____21361),
                 FStar_Syntax_Syntax.Tm_arrow uu____21362) ->
                  solve_t' env
                    (let uu___3354_21414 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3354_21414.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3354_21414.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3354_21414.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3354_21414.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3354_21414.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3354_21414.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3354_21414.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3354_21414.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3354_21414.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21415, FStar_Syntax_Syntax.Tm_uvar uu____21416) ->
                  let uu____21429 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21429
              | (uu____21430, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21431;
                    FStar_Syntax_Syntax.pos = uu____21432;
                    FStar_Syntax_Syntax.vars = uu____21433;_},
                  uu____21434)) ->
                  let uu____21471 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21471
              | (FStar_Syntax_Syntax.Tm_uvar uu____21472, uu____21473) ->
                  let uu____21486 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21486
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21487;
                    FStar_Syntax_Syntax.pos = uu____21488;
                    FStar_Syntax_Syntax.vars = uu____21489;_},
                  uu____21490),
                 uu____21491) ->
                  let uu____21528 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21528
              | (FStar_Syntax_Syntax.Tm_refine uu____21529, uu____21530) ->
                  let t21 =
                    let uu____21538 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____21538 in
                  solve_t env
                    (let uu___3389_21564 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3389_21564.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3389_21564.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3389_21564.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3389_21564.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3389_21564.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3389_21564.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3389_21564.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3389_21564.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3389_21564.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21565, FStar_Syntax_Syntax.Tm_refine uu____21566) ->
                  let t11 =
                    let uu____21574 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____21574 in
                  solve_t env
                    (let uu___3396_21600 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3396_21600.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3396_21600.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3396_21600.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3396_21600.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3396_21600.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3396_21600.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3396_21600.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3396_21600.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3396_21600.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____21682 =
                    let uu____21683 = guard_of_prob env wl problem t1 t2 in
                    match uu____21683 with
                    | (guard, wl1) ->
                        let uu____21690 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____21690 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____21909 = br1 in
                        (match uu____21909 with
                         | (p1, w1, uu____21938) ->
                             let uu____21955 = br2 in
                             (match uu____21955 with
                              | (p2, w2, uu____21978) ->
                                  let uu____21983 =
                                    let uu____21984 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____21984 in
                                  if uu____21983
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____22008 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____22008 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____22045 = br2 in
                                         (match uu____22045 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____22078 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____22078 in
                                              let uu____22083 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____22114,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____22135) ->
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
                                                    let uu____22194 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____22194 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____22083
                                                (fun uu____22265 ->
                                                   match uu____22265 with
                                                   | (wprobs, wl2) ->
                                                       let uu____22302 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____22302
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____22322
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____22322
                                                              then
                                                                let uu____22323
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____22324
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____22323
                                                                  uu____22324
                                                              else ());
                                                             (let uu____22326
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____22326
                                                                (fun
                                                                   uu____22362
                                                                   ->
                                                                   match uu____22362
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
                    | uu____22491 -> FStar_Pervasives_Native.None in
                  let uu____22532 = solve_branches wl brs1 brs2 in
                  (match uu____22532 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____22556 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____22556 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____22581 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____22581 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____22614 =
                                FStar_List.map
                                  (fun uu____22626 ->
                                     match uu____22626 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____22614 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____22635 =
                              let uu____22636 =
                                let uu____22637 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____22637
                                  (let uu___3495_22645 = wl3 in
                                   {
                                     attempting =
                                       (uu___3495_22645.attempting);
                                     wl_deferred =
                                       (uu___3495_22645.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3495_22645.wl_deferred_to_tac);
                                     ctr = (uu___3495_22645.ctr);
                                     defer_ok = (uu___3495_22645.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3495_22645.umax_heuristic_ok);
                                     tcenv = (uu___3495_22645.tcenv);
                                     wl_implicits =
                                       (uu___3495_22645.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3495_22645.repr_subcomp_allowed)
                                   }) in
                              solve env uu____22636 in
                            (match uu____22635 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____22650 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____22657 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____22657 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____22658, uu____22659) ->
                  let head1 =
                    let uu____22683 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22683
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22729 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22729
                      FStar_Pervasives_Native.fst in
                  ((let uu____22775 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22775
                    then
                      let uu____22776 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22777 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22778 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22776 uu____22777 uu____22778
                    else ());
                   (let no_free_uvars t =
                      (let uu____22788 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22788) &&
                        (let uu____22792 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22792) in
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
                      let uu____22808 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22808 = FStar_Syntax_Util.Equal in
                    let uu____22809 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22809
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22810 = equal t1 t2 in
                         (if uu____22810
                          then
                            let uu____22811 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22811
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22814 =
                            let uu____22821 = equal t1 t2 in
                            if uu____22821
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22831 = mk_eq2 wl env orig t1 t2 in
                               match uu____22831 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22814 with
                          | (guard, wl1) ->
                              let uu____22852 = solve_prob orig guard [] wl1 in
                              solve env uu____22852))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____22854, uu____22855) ->
                  let head1 =
                    let uu____22863 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22863
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22909 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22909
                      FStar_Pervasives_Native.fst in
                  ((let uu____22955 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22955
                    then
                      let uu____22956 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22957 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22958 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22956 uu____22957 uu____22958
                    else ());
                   (let no_free_uvars t =
                      (let uu____22968 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22968) &&
                        (let uu____22972 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22972) in
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
                      let uu____22988 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22988 = FStar_Syntax_Util.Equal in
                    let uu____22989 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22989
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22990 = equal t1 t2 in
                         (if uu____22990
                          then
                            let uu____22991 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22991
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22994 =
                            let uu____23001 = equal t1 t2 in
                            if uu____23001
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23011 = mk_eq2 wl env orig t1 t2 in
                               match uu____23011 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22994 with
                          | (guard, wl1) ->
                              let uu____23032 = solve_prob orig guard [] wl1 in
                              solve env uu____23032))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____23034, uu____23035) ->
                  let head1 =
                    let uu____23037 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23037
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23083 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23083
                      FStar_Pervasives_Native.fst in
                  ((let uu____23129 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23129
                    then
                      let uu____23130 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23131 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23132 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23130 uu____23131 uu____23132
                    else ());
                   (let no_free_uvars t =
                      (let uu____23142 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23142) &&
                        (let uu____23146 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23146) in
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
                      let uu____23162 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23162 = FStar_Syntax_Util.Equal in
                    let uu____23163 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23163
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23164 = equal t1 t2 in
                         (if uu____23164
                          then
                            let uu____23165 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23165
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23168 =
                            let uu____23175 = equal t1 t2 in
                            if uu____23175
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23185 = mk_eq2 wl env orig t1 t2 in
                               match uu____23185 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23168 with
                          | (guard, wl1) ->
                              let uu____23206 = solve_prob orig guard [] wl1 in
                              solve env uu____23206))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____23208, uu____23209) ->
                  let head1 =
                    let uu____23211 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23211
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23257 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23257
                      FStar_Pervasives_Native.fst in
                  ((let uu____23303 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23303
                    then
                      let uu____23304 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23305 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23306 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23304 uu____23305 uu____23306
                    else ());
                   (let no_free_uvars t =
                      (let uu____23316 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23316) &&
                        (let uu____23320 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23320) in
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
                      let uu____23336 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23336 = FStar_Syntax_Util.Equal in
                    let uu____23337 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23337
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23338 = equal t1 t2 in
                         (if uu____23338
                          then
                            let uu____23339 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23339
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23342 =
                            let uu____23349 = equal t1 t2 in
                            if uu____23349
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23359 = mk_eq2 wl env orig t1 t2 in
                               match uu____23359 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23342 with
                          | (guard, wl1) ->
                              let uu____23380 = solve_prob orig guard [] wl1 in
                              solve env uu____23380))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____23382, uu____23383) ->
                  let head1 =
                    let uu____23385 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23385
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23425 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23425
                      FStar_Pervasives_Native.fst in
                  ((let uu____23465 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23465
                    then
                      let uu____23466 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23467 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23468 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23466 uu____23467 uu____23468
                    else ());
                   (let no_free_uvars t =
                      (let uu____23478 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23478) &&
                        (let uu____23482 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23482) in
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
                      let uu____23498 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23498 = FStar_Syntax_Util.Equal in
                    let uu____23499 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23499
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23500 = equal t1 t2 in
                         (if uu____23500
                          then
                            let uu____23501 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23501
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23504 =
                            let uu____23511 = equal t1 t2 in
                            if uu____23511
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23521 = mk_eq2 wl env orig t1 t2 in
                               match uu____23521 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23504 with
                          | (guard, wl1) ->
                              let uu____23542 = solve_prob orig guard [] wl1 in
                              solve env uu____23542))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____23544, uu____23545) ->
                  let head1 =
                    let uu____23563 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23563
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23603 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23603
                      FStar_Pervasives_Native.fst in
                  ((let uu____23643 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23643
                    then
                      let uu____23644 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23645 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23646 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23644 uu____23645 uu____23646
                    else ());
                   (let no_free_uvars t =
                      (let uu____23656 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23656) &&
                        (let uu____23660 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23660) in
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
                      let uu____23676 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23676 = FStar_Syntax_Util.Equal in
                    let uu____23677 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23677
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23678 = equal t1 t2 in
                         (if uu____23678
                          then
                            let uu____23679 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23679
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23682 =
                            let uu____23689 = equal t1 t2 in
                            if uu____23689
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23699 = mk_eq2 wl env orig t1 t2 in
                               match uu____23699 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23682 with
                          | (guard, wl1) ->
                              let uu____23720 = solve_prob orig guard [] wl1 in
                              solve env uu____23720))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23722, FStar_Syntax_Syntax.Tm_match uu____23723) ->
                  let head1 =
                    let uu____23747 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23747
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23787 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23787
                      FStar_Pervasives_Native.fst in
                  ((let uu____23827 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23827
                    then
                      let uu____23828 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23829 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23830 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23828 uu____23829 uu____23830
                    else ());
                   (let no_free_uvars t =
                      (let uu____23840 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23840) &&
                        (let uu____23844 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23844) in
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
                      let uu____23860 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23860 = FStar_Syntax_Util.Equal in
                    let uu____23861 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23861
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23862 = equal t1 t2 in
                         (if uu____23862
                          then
                            let uu____23863 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23863
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23866 =
                            let uu____23873 = equal t1 t2 in
                            if uu____23873
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23883 = mk_eq2 wl env orig t1 t2 in
                               match uu____23883 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23866 with
                          | (guard, wl1) ->
                              let uu____23904 = solve_prob orig guard [] wl1 in
                              solve env uu____23904))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23906, FStar_Syntax_Syntax.Tm_uinst uu____23907) ->
                  let head1 =
                    let uu____23915 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23915
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23955 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23955
                      FStar_Pervasives_Native.fst in
                  ((let uu____23995 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23995
                    then
                      let uu____23996 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23997 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23998 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23996 uu____23997 uu____23998
                    else ());
                   (let no_free_uvars t =
                      (let uu____24008 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24008) &&
                        (let uu____24012 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24012) in
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
                      let uu____24028 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24028 = FStar_Syntax_Util.Equal in
                    let uu____24029 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24029
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24030 = equal t1 t2 in
                         (if uu____24030
                          then
                            let uu____24031 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24031
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24034 =
                            let uu____24041 = equal t1 t2 in
                            if uu____24041
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24051 = mk_eq2 wl env orig t1 t2 in
                               match uu____24051 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24034 with
                          | (guard, wl1) ->
                              let uu____24072 = solve_prob orig guard [] wl1 in
                              solve env uu____24072))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24074, FStar_Syntax_Syntax.Tm_name uu____24075) ->
                  let head1 =
                    let uu____24077 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24077
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24117 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24117
                      FStar_Pervasives_Native.fst in
                  ((let uu____24157 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24157
                    then
                      let uu____24158 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24159 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24160 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24158 uu____24159 uu____24160
                    else ());
                   (let no_free_uvars t =
                      (let uu____24170 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24170) &&
                        (let uu____24174 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24174) in
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
                      let uu____24190 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24190 = FStar_Syntax_Util.Equal in
                    let uu____24191 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24191
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24192 = equal t1 t2 in
                         (if uu____24192
                          then
                            let uu____24193 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24193
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24196 =
                            let uu____24203 = equal t1 t2 in
                            if uu____24203
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24213 = mk_eq2 wl env orig t1 t2 in
                               match uu____24213 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24196 with
                          | (guard, wl1) ->
                              let uu____24234 = solve_prob orig guard [] wl1 in
                              solve env uu____24234))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24236, FStar_Syntax_Syntax.Tm_constant uu____24237) ->
                  let head1 =
                    let uu____24239 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24239
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24279 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24279
                      FStar_Pervasives_Native.fst in
                  ((let uu____24319 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24319
                    then
                      let uu____24320 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24321 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24322 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24320 uu____24321 uu____24322
                    else ());
                   (let no_free_uvars t =
                      (let uu____24332 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24332) &&
                        (let uu____24336 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24336) in
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
                      let uu____24352 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24352 = FStar_Syntax_Util.Equal in
                    let uu____24353 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24353
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24354 = equal t1 t2 in
                         (if uu____24354
                          then
                            let uu____24355 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24355
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24358 =
                            let uu____24365 = equal t1 t2 in
                            if uu____24365
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24375 = mk_eq2 wl env orig t1 t2 in
                               match uu____24375 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24358 with
                          | (guard, wl1) ->
                              let uu____24396 = solve_prob orig guard [] wl1 in
                              solve env uu____24396))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24398, FStar_Syntax_Syntax.Tm_fvar uu____24399) ->
                  let head1 =
                    let uu____24401 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24401
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24447 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24447
                      FStar_Pervasives_Native.fst in
                  ((let uu____24493 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24493
                    then
                      let uu____24494 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24495 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24496 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24494 uu____24495 uu____24496
                    else ());
                   (let no_free_uvars t =
                      (let uu____24506 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24506) &&
                        (let uu____24510 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24510) in
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
                      let uu____24526 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24526 = FStar_Syntax_Util.Equal in
                    let uu____24527 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24527
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24528 = equal t1 t2 in
                         (if uu____24528
                          then
                            let uu____24529 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24529
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24532 =
                            let uu____24539 = equal t1 t2 in
                            if uu____24539
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24549 = mk_eq2 wl env orig t1 t2 in
                               match uu____24549 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24532 with
                          | (guard, wl1) ->
                              let uu____24570 = solve_prob orig guard [] wl1 in
                              solve env uu____24570))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24572, FStar_Syntax_Syntax.Tm_app uu____24573) ->
                  let head1 =
                    let uu____24591 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24591
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24631 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24631
                      FStar_Pervasives_Native.fst in
                  ((let uu____24671 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24671
                    then
                      let uu____24672 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24673 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24674 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24672 uu____24673 uu____24674
                    else ());
                   (let no_free_uvars t =
                      (let uu____24684 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24684) &&
                        (let uu____24688 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24688) in
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
                      let uu____24704 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24704 = FStar_Syntax_Util.Equal in
                    let uu____24705 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24705
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24706 = equal t1 t2 in
                         (if uu____24706
                          then
                            let uu____24707 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24707
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24710 =
                            let uu____24717 = equal t1 t2 in
                            if uu____24717
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24727 = mk_eq2 wl env orig t1 t2 in
                               match uu____24727 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24710 with
                          | (guard, wl1) ->
                              let uu____24748 = solve_prob orig guard [] wl1 in
                              solve env uu____24748))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____24750,
                 FStar_Syntax_Syntax.Tm_let uu____24751) ->
                  let uu____24776 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____24776
                  then
                    let uu____24777 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____24777
                  else
                    (let uu____24779 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____24779 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____24780, uu____24781) ->
                  let uu____24794 =
                    let uu____24799 =
                      let uu____24800 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24801 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24802 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24803 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24800 uu____24801 uu____24802 uu____24803 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24799) in
                  FStar_Errors.raise_error uu____24794
                    t1.FStar_Syntax_Syntax.pos
              | (uu____24804, FStar_Syntax_Syntax.Tm_let uu____24805) ->
                  let uu____24818 =
                    let uu____24823 =
                      let uu____24824 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24825 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24826 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24827 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24824 uu____24825 uu____24826 uu____24827 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24823) in
                  FStar_Errors.raise_error uu____24818
                    t1.FStar_Syntax_Syntax.pos
              | uu____24828 ->
                  let uu____24833 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____24833 orig))))
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
          (let uu____24895 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____24895
           then
             let uu____24896 =
               let uu____24897 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____24897 in
             let uu____24898 =
               let uu____24899 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____24899 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____24896 uu____24898
           else ());
          (let uu____24901 =
             let uu____24902 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____24902 in
           if uu____24901
           then
             let uu____24903 =
               mklstr
                 (fun uu____24910 ->
                    let uu____24911 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____24912 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____24911 uu____24912) in
             giveup env uu____24903 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____24930 =
                  mklstr
                    (fun uu____24937 ->
                       let uu____24938 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____24939 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____24938 uu____24939) in
                giveup env uu____24930 orig)
             else
               (let uu____24941 =
                  FStar_List.fold_left2
                    (fun uu____24962 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____24962 with
                           | (univ_sub_probs, wl1) ->
                               let uu____24983 =
                                 let uu____24988 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____24989 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____24988
                                   FStar_TypeChecker_Common.EQ uu____24989
                                   "effect universes" in
                               (match uu____24983 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____24941 with
                | (univ_sub_probs, wl1) ->
                    let uu____25008 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____25008 with
                     | (ret_sub_prob, wl2) ->
                         let uu____25015 =
                           FStar_List.fold_right2
                             (fun uu____25052 ->
                                fun uu____25053 ->
                                  fun uu____25054 ->
                                    match (uu____25052, uu____25053,
                                            uu____25054)
                                    with
                                    | ((a1, uu____25098), (a2, uu____25100),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____25133 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____25133 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____25015 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____25159 =
                                  let uu____25162 =
                                    let uu____25165 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____25165 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____25162 in
                                FStar_List.append univ_sub_probs uu____25159 in
                              let guard =
                                let guard =
                                  let uu____25184 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____25184 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3648_25193 = wl3 in
                                {
                                  attempting = (uu___3648_25193.attempting);
                                  wl_deferred = (uu___3648_25193.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3648_25193.wl_deferred_to_tac);
                                  ctr = (uu___3648_25193.ctr);
                                  defer_ok = (uu___3648_25193.defer_ok);
                                  smt_ok = (uu___3648_25193.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3648_25193.umax_heuristic_ok);
                                  tcenv = (uu___3648_25193.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3648_25193.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____25195 = attempt sub_probs wl5 in
                              solve env uu____25195)))) in
        let solve_layered_sub c11 c21 =
          (let uu____25208 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____25208
           then
             let uu____25209 =
               let uu____25210 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25210
                 FStar_Syntax_Print.comp_to_string in
             let uu____25211 =
               let uu____25212 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25212
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____25209 uu____25211
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____25217 =
                 let uu____25218 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25218 FStar_Ident.string_of_id in
               let uu____25219 =
                 let uu____25220 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25220 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____25217 uu____25219 in
             let lift_c1 edge =
               let uu____25235 =
                 let uu____25240 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____25240
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____25235
                 (fun uu____25257 ->
                    match uu____25257 with
                    | (c, g) ->
                        let uu____25268 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____25268, g)) in
             let uu____25269 =
               let uu____25280 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____25280 with
               | FStar_Pervasives_Native.None ->
                   let uu____25293 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____25293 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____25309 = lift_c1 edge in
                        (match uu____25309 with
                         | (c12, g_lift) ->
                             let uu____25326 =
                               let uu____25329 =
                                 let uu____25330 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____25330
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____25329
                                 (fun ts ->
                                    let uu____25336 =
                                      let uu____25337 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____25337
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____25336
                                      (fun uu____25348 ->
                                         FStar_Pervasives_Native.Some
                                           uu____25348)) in
                             (c12, g_lift, uu____25326, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____25352 =
                     let uu____25355 =
                       let uu____25356 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____25356
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____25355
                       (fun uu____25367 ->
                          FStar_Pervasives_Native.Some uu____25367) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____25352,
                     true) in
             match uu____25269 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____25378 =
                     mklstr
                       (fun uu____25385 ->
                          let uu____25386 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____25387 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____25386 uu____25387) in
                   giveup env uu____25378 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3683_25393 = wl in
                      {
                        attempting = (uu___3683_25393.attempting);
                        wl_deferred = (uu___3683_25393.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3683_25393.wl_deferred_to_tac);
                        ctr = (uu___3683_25393.ctr);
                        defer_ok = (uu___3683_25393.defer_ok);
                        smt_ok = (uu___3683_25393.smt_ok);
                        umax_heuristic_ok =
                          (uu___3683_25393.umax_heuristic_ok);
                        tcenv = (uu___3683_25393.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3683_25393.repr_subcomp_allowed)
                      } in
                    let uu____25394 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____25416 =
                             let uu____25417 = FStar_Syntax_Subst.compress t in
                             uu____25417.FStar_Syntax_Syntax.n in
                           match uu____25416 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____25420 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____25434)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____25440) ->
                               is_uvar t1
                           | uu____25465 -> false in
                         FStar_List.fold_right2
                           (fun uu____25498 ->
                              fun uu____25499 ->
                                fun uu____25500 ->
                                  match (uu____25498, uu____25499,
                                          uu____25500)
                                  with
                                  | ((a1, uu____25544), (a2, uu____25546),
                                     (is_sub_probs, wl2)) ->
                                      let uu____25579 = is_uvar a1 in
                                      if uu____25579
                                      then
                                        ((let uu____25587 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____25587
                                          then
                                            let uu____25588 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____25589 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____25588 uu____25589
                                          else ());
                                         (let uu____25591 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____25591 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____25394 with
                    | (is_sub_probs, wl2) ->
                        let uu____25617 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____25617 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____25630 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____25631 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____25630 s uu____25631 in
                             let uu____25632 =
                               let uu____25661 =
                                 let uu____25662 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____25662.FStar_Syntax_Syntax.n in
                               match uu____25661 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____25721 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____25721 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____25784 =
                                          let uu____25803 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____25803
                                            (fun uu____25906 ->
                                               match uu____25906 with
                                               | (l1, l2) ->
                                                   let uu____25979 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____25979)) in
                                        (match uu____25784 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____26084 ->
                                   let uu____26085 =
                                     let uu____26090 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____26090) in
                                   FStar_Errors.raise_error uu____26085 r in
                             (match uu____25632 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____26163 =
                                    let uu____26170 =
                                      let uu____26171 =
                                        let uu____26172 =
                                          let uu____26179 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____26179,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____26172 in
                                      [uu____26171] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____26170
                                      (fun b ->
                                         let uu____26195 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____26196 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____26197 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____26195 uu____26196
                                           uu____26197) r in
                                  (match uu____26163 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3748_26205 = wl3 in
                                         {
                                           attempting =
                                             (uu___3748_26205.attempting);
                                           wl_deferred =
                                             (uu___3748_26205.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3748_26205.wl_deferred_to_tac);
                                           ctr = (uu___3748_26205.ctr);
                                           defer_ok =
                                             (uu___3748_26205.defer_ok);
                                           smt_ok = (uu___3748_26205.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3748_26205.umax_heuristic_ok);
                                           tcenv = (uu___3748_26205.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3748_26205.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____26230 =
                                                  let uu____26237 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____26237, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____26230) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____26254 =
                                         let f_sort_is =
                                           let uu____26264 =
                                             let uu____26267 =
                                               let uu____26268 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____26268.FStar_Syntax_Syntax.sort in
                                             let uu____26277 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____26278 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____26267 uu____26277 r
                                               uu____26278 in
                                           FStar_All.pipe_right uu____26264
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____26283 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____26319 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____26319 with
                                                  | (ps, wl5) ->
                                                      ((let uu____26341 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____26341
                                                        then
                                                          let uu____26342 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____26343 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____26342
                                                            uu____26343
                                                        else ());
                                                       (let uu____26345 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____26345
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____26283 in
                                       (match uu____26254 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____26369 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____26369
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____26370 =
                                              let g_sort_is =
                                                let uu____26380 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____26381 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____26380 r uu____26381 in
                                              let uu____26382 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____26418 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____26418 with
                                                       | (ps, wl6) ->
                                                           ((let uu____26440
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____26440
                                                             then
                                                               let uu____26441
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____26442
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____26441
                                                                 uu____26442
                                                             else ());
                                                            (let uu____26444
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____26444
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____26382 in
                                            (match uu____26370 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____26470 =
                                                     let uu____26475 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____26476 =
                                                       let uu____26477 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____26477 in
                                                     (uu____26475,
                                                       uu____26476) in
                                                   match uu____26470 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____26505 =
                                                     let uu____26508 =
                                                       let uu____26511 =
                                                         let uu____26514 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____26514 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____26511 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____26508 in
                                                   ret_sub_prob ::
                                                     uu____26505 in
                                                 let guard =
                                                   let guard =
                                                     let uu____26535 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____26535 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____26546 =
                                                     let uu____26549 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____26552 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____26552)
                                                       uu____26549 in
                                                   solve_prob orig
                                                     uu____26546 [] wl6 in
                                                 let uu____26553 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____26553))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____26578 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____26580 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____26580]
               | x -> x in
             let c12 =
               let uu___3806_26583 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3806_26583.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3806_26583.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3806_26583.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3806_26583.FStar_Syntax_Syntax.flags)
               } in
             let uu____26584 =
               let uu____26589 =
                 FStar_All.pipe_right
                   (let uu___3809_26591 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3809_26591.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3809_26591.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3809_26591.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3809_26591.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____26589
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____26584
               (fun uu____26605 ->
                  match uu____26605 with
                  | (c, g) ->
                      let uu____26612 =
                        let uu____26613 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____26613 in
                      if uu____26612
                      then
                        let uu____26614 =
                          let uu____26619 =
                            let uu____26620 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____26621 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____26620 uu____26621 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____26619) in
                        FStar_Errors.raise_error uu____26614 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____26623 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____26625 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____26625))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____26623
           then
             let uu____26626 =
               mklstr
                 (fun uu____26633 ->
                    let uu____26634 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____26635 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____26634 uu____26635) in
             giveup env uu____26626 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_26641 ->
                        match uu___29_26641 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____26642 -> false)) in
              let uu____26643 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____26673)::uu____26674,
                   (wp2, uu____26676)::uu____26677) -> (wp1, wp2)
                | uu____26750 ->
                    let uu____26775 =
                      let uu____26780 =
                        let uu____26781 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____26782 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____26781 uu____26782 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____26780) in
                    FStar_Errors.raise_error uu____26775
                      env.FStar_TypeChecker_Env.range in
              match uu____26643 with
              | (wpc1, wpc2) ->
                  let uu____26789 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____26789
                  then
                    let uu____26790 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____26790 wl
                  else
                    (let uu____26792 =
                       let uu____26799 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____26799 in
                     match uu____26792 with
                     | (c2_decl, qualifiers) ->
                         let uu____26820 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____26820
                         then
                           let c1_repr =
                             let uu____26824 =
                               let uu____26825 =
                                 let uu____26826 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____26826 in
                               let uu____26827 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26825 uu____26827 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26824 in
                           let c2_repr =
                             let uu____26829 =
                               let uu____26830 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____26831 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26830 uu____26831 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26829 in
                           let uu____26832 =
                             let uu____26837 =
                               let uu____26838 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____26839 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____26838 uu____26839 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____26837 in
                           (match uu____26832 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____26843 = attempt [prob] wl2 in
                                solve env uu____26843)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____26860 = lift_c1 () in
                                   FStar_All.pipe_right uu____26860
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____26882 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____26882
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____26886 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____26886 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____26892 =
                                       let uu____26893 =
                                         let uu____26910 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____26913 =
                                           let uu____26924 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____26924; wpc1_2] in
                                         (uu____26910, uu____26913) in
                                       FStar_Syntax_Syntax.Tm_app uu____26893 in
                                     FStar_Syntax_Syntax.mk uu____26892 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____26972 =
                                      let uu____26973 =
                                        let uu____26990 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____26993 =
                                          let uu____27004 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____27013 =
                                            let uu____27024 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____27024; wpc1_2] in
                                          uu____27004 :: uu____27013 in
                                        (uu____26990, uu____26993) in
                                      FStar_Syntax_Syntax.Tm_app uu____26973 in
                                    FStar_Syntax_Syntax.mk uu____26972 r)) in
                            (let uu____27078 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____27078
                             then
                               let uu____27079 =
                                 let uu____27080 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____27080 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____27079
                             else ());
                            (let uu____27082 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____27082 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____27090 =
                                     let uu____27093 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____27096 ->
                                          FStar_Pervasives_Native.Some
                                            uu____27096) uu____27093 in
                                   solve_prob orig uu____27090 [] wl1 in
                                 let uu____27097 = attempt [base_prob] wl2 in
                                 solve env uu____27097))))) in
        let uu____27098 = FStar_Util.physical_equality c1 c2 in
        if uu____27098
        then
          let uu____27099 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____27099
        else
          ((let uu____27102 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____27102
            then
              let uu____27103 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____27104 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____27103
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____27104
            else ());
           (let uu____27106 =
              let uu____27115 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____27118 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____27115, uu____27118) in
            match uu____27106 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____27136),
                    FStar_Syntax_Syntax.Total (t2, uu____27138)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____27155 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27155 wl
                 | (FStar_Syntax_Syntax.GTotal uu____27156,
                    FStar_Syntax_Syntax.Total uu____27157) ->
                     let uu____27174 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____27174 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____27176),
                    FStar_Syntax_Syntax.Total (t2, uu____27178)) ->
                     let uu____27195 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27195 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____27197),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27199)) ->
                     let uu____27216 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27216 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27218),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27220)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____27237 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27237 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27239),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27241)) ->
                     let uu____27258 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____27258 orig
                 | (FStar_Syntax_Syntax.GTotal uu____27259,
                    FStar_Syntax_Syntax.Comp uu____27260) ->
                     let uu____27269 =
                       let uu___3933_27272 = problem in
                       let uu____27275 =
                         let uu____27276 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27276 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3933_27272.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27275;
                         FStar_TypeChecker_Common.relation =
                           (uu___3933_27272.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3933_27272.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3933_27272.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3933_27272.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3933_27272.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3933_27272.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3933_27272.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3933_27272.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27269 wl
                 | (FStar_Syntax_Syntax.Total uu____27277,
                    FStar_Syntax_Syntax.Comp uu____27278) ->
                     let uu____27287 =
                       let uu___3933_27290 = problem in
                       let uu____27293 =
                         let uu____27294 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27294 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3933_27290.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27293;
                         FStar_TypeChecker_Common.relation =
                           (uu___3933_27290.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3933_27290.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3933_27290.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3933_27290.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3933_27290.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3933_27290.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3933_27290.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3933_27290.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27287 wl
                 | (FStar_Syntax_Syntax.Comp uu____27295,
                    FStar_Syntax_Syntax.GTotal uu____27296) ->
                     let uu____27305 =
                       let uu___3945_27308 = problem in
                       let uu____27311 =
                         let uu____27312 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27312 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3945_27308.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3945_27308.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3945_27308.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27311;
                         FStar_TypeChecker_Common.element =
                           (uu___3945_27308.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3945_27308.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3945_27308.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3945_27308.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3945_27308.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3945_27308.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27305 wl
                 | (FStar_Syntax_Syntax.Comp uu____27313,
                    FStar_Syntax_Syntax.Total uu____27314) ->
                     let uu____27323 =
                       let uu___3945_27326 = problem in
                       let uu____27329 =
                         let uu____27330 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27330 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3945_27326.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3945_27326.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3945_27326.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27329;
                         FStar_TypeChecker_Common.element =
                           (uu___3945_27326.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3945_27326.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3945_27326.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3945_27326.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3945_27326.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3945_27326.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27323 wl
                 | (FStar_Syntax_Syntax.Comp uu____27331,
                    FStar_Syntax_Syntax.Comp uu____27332) ->
                     let uu____27333 =
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
                     if uu____27333
                     then
                       let uu____27334 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____27334 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27338 =
                            let uu____27343 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____27343
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27349 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____27350 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____27349, uu____27350)) in
                          match uu____27338 with
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
                           (let uu____27357 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____27357
                            then
                              let uu____27358 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____27359 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____27358 uu____27359
                            else ());
                           (let uu____27361 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____27361
                            then solve_layered_sub c12 c22
                            else
                              (let uu____27363 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____27363 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____27366 =
                                     mklstr
                                       (fun uu____27373 ->
                                          let uu____27374 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____27375 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____27374 uu____27375) in
                                   giveup env uu____27366 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____27382 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____27382 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____27423 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____27423 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____27441 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27469 ->
                match uu____27469 with
                | (u1, u2) ->
                    let uu____27476 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____27477 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____27476 uu____27477)) in
      FStar_All.pipe_right uu____27441 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial, [], (uu____27504, [])) when
          let uu____27529 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____27529 -> "{}"
      | uu____27530 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27553 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____27553
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____27573 =
              FStar_List.map
                (fun uu____27584 ->
                   match uu____27584 with
                   | (msg, x) ->
                       let uu____27591 =
                         let uu____27592 = prob_to_string env x in
                         Prims.op_Hat ": " uu____27592 in
                       Prims.op_Hat msg uu____27591) defs in
            FStar_All.pipe_right uu____27573 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____27596 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____27597 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____27598 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____27596 uu____27597 uu____27598 imps
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
                  let uu____27651 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____27651
                  then
                    let uu____27652 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____27653 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27652
                      (rel_to_string rel) uu____27653
                  else "TOP" in
                let uu____27655 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____27655 with
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
              let uu____27713 =
                let uu____27716 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____27719 ->
                     FStar_Pervasives_Native.Some uu____27719) uu____27716 in
              FStar_Syntax_Syntax.new_bv uu____27713 t1 in
            let uu____27720 =
              let uu____27725 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27725 in
            match uu____27720 with | (p, wl1) -> (p, x, wl1)
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
        (let uu____27796 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____27796
         then
           let uu____27797 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____27797
         else ());
        (let uu____27801 =
           FStar_Util.record_time (fun uu____27807 -> solve env probs) in
         match uu____27801 with
         | (sol, ms) ->
             ((let uu____27819 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____27819
               then
                 let uu____27820 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____27820
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____27833 =
                     FStar_Util.record_time
                       (fun uu____27839 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____27833 with
                    | ((), ms1) ->
                        ((let uu____27850 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____27850
                          then
                            let uu____27851 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____27851
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____27862 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____27862
                     then
                       let uu____27863 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____27863
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
          ((let uu____27887 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____27887
            then
              let uu____27888 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27888
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____27892 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____27892
             then
               let uu____27893 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27893
             else ());
            (let f2 =
               let uu____27896 =
                 let uu____27897 = FStar_Syntax_Util.unmeta f1 in
                 uu____27897.FStar_Syntax_Syntax.n in
               match uu____27896 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27901 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4065_27902 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4065_27902.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4065_27902.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4065_27902.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4065_27902.FStar_TypeChecker_Common.implicits)
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
            let uu____27953 =
              let uu____27954 =
                let uu____27955 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____27956 ->
                       FStar_TypeChecker_Common.NonTrivial uu____27956) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____27955;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____27954 in
            FStar_All.pipe_left
              (fun uu____27963 -> FStar_Pervasives_Native.Some uu____27963)
              uu____27953
let with_guard_no_simp :
  'uuuuuu27972 .
    'uuuuuu27972 ->
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
            let uu____28021 =
              let uu____28022 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____28023 ->
                     FStar_TypeChecker_Common.NonTrivial uu____28023) in
              {
                FStar_TypeChecker_Common.guard_f = uu____28022;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____28021
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
          (let uu____28053 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____28053
           then
             let uu____28054 = FStar_Syntax_Print.term_to_string t1 in
             let uu____28055 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____28054
               uu____28055
           else ());
          (let uu____28057 =
             let uu____28062 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____28062 in
           match uu____28057 with
           | (prob, wl) ->
               let g =
                 let uu____28070 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____28080 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____28070 in
               ((let uu____28102 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____28102
                 then
                   let uu____28103 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____28103
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
        let uu____28120 = try_teq true env t1 t2 in
        match uu____28120 with
        | FStar_Pervasives_Native.None ->
            ((let uu____28124 = FStar_TypeChecker_Env.get_range env in
              let uu____28125 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____28124 uu____28125);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____28132 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____28132
              then
                let uu____28133 = FStar_Syntax_Print.term_to_string t1 in
                let uu____28134 = FStar_Syntax_Print.term_to_string t2 in
                let uu____28135 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____28133
                  uu____28134 uu____28135
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
        (let uu____28155 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____28155
         then
           let uu____28156 = FStar_Syntax_Print.term_to_string t1 in
           let uu____28157 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____28156
             uu____28157
         else ());
        (let uu____28159 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____28159 with
         | (prob, x, wl) ->
             let g =
               let uu____28174 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____28184 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____28174 in
             ((let uu____28206 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____28206
               then
                 let uu____28207 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____28207
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____28212 =
                     let uu____28213 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____28213 g1 in
                   FStar_Pervasives_Native.Some uu____28212)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____28234 = FStar_TypeChecker_Env.get_range env in
          let uu____28235 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____28234 uu____28235
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
        (let uu____28260 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____28260
         then
           let uu____28261 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____28262 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28261 uu____28262
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28265 =
           let uu____28272 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28272 "sub_comp" in
         match uu____28265 with
         | (prob, wl) ->
             let wl1 =
               let uu___4138_28282 = wl in
               {
                 attempting = (uu___4138_28282.attempting);
                 wl_deferred = (uu___4138_28282.wl_deferred);
                 wl_deferred_to_tac = (uu___4138_28282.wl_deferred_to_tac);
                 ctr = (uu___4138_28282.ctr);
                 defer_ok = (uu___4138_28282.defer_ok);
                 smt_ok = (uu___4138_28282.smt_ok);
                 umax_heuristic_ok = (uu___4138_28282.umax_heuristic_ok);
                 tcenv = (uu___4138_28282.tcenv);
                 wl_implicits = (uu___4138_28282.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____28285 =
                 FStar_Util.record_time
                   (fun uu____28296 ->
                      let uu____28297 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____28307 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____28297) in
               match uu____28285 with
               | (r, ms) ->
                   ((let uu____28337 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____28337
                     then
                       let uu____28338 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____28339 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____28340 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28338 uu____28339
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28340
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
      fun uu____28369 ->
        match uu____28369 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28412 =
                 let uu____28417 =
                   let uu____28418 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____28419 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28418 uu____28419 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28417) in
               let uu____28420 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____28412 uu____28420) in
            let equiv v v' =
              let uu____28432 =
                let uu____28437 = FStar_Syntax_Subst.compress_univ v in
                let uu____28438 = FStar_Syntax_Subst.compress_univ v' in
                (uu____28437, uu____28438) in
              match uu____28432 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28461 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____28491 = FStar_Syntax_Subst.compress_univ v in
                      match uu____28491 with
                      | FStar_Syntax_Syntax.U_unif uu____28498 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28529 ->
                                    match uu____28529 with
                                    | (u, v') ->
                                        let uu____28538 = equiv v v' in
                                        if uu____28538
                                        then
                                          let uu____28541 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____28541 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____28557 -> [])) in
            let uu____28562 =
              let wl =
                let uu___4181_28566 = empty_worklist env in
                {
                  attempting = (uu___4181_28566.attempting);
                  wl_deferred = (uu___4181_28566.wl_deferred);
                  wl_deferred_to_tac = (uu___4181_28566.wl_deferred_to_tac);
                  ctr = (uu___4181_28566.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4181_28566.smt_ok);
                  umax_heuristic_ok = (uu___4181_28566.umax_heuristic_ok);
                  tcenv = (uu___4181_28566.tcenv);
                  wl_implicits = (uu___4181_28566.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4181_28566.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28584 ->
                      match uu____28584 with
                      | (lb, v) ->
                          let uu____28591 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____28591 with
                           | USolved wl1 -> ()
                           | uu____28593 -> fail lb v))) in
            let rec check_ineq uu____28603 =
              match uu____28603 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____28612) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____28639,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____28641,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____28654) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____28661, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____28669 -> false) in
            let uu____28674 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28689 ->
                      match uu____28689 with
                      | (u, v) ->
                          let uu____28696 = check_ineq (u, v) in
                          if uu____28696
                          then true
                          else
                            ((let uu____28699 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____28699
                              then
                                let uu____28700 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____28701 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____28700
                                  uu____28701
                              else ());
                             false))) in
            if uu____28674
            then ()
            else
              ((let uu____28705 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____28705
                then
                  ((let uu____28707 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28707);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28717 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28717))
                else ());
               (let uu____28727 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28727))
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
          let fail uu____28801 =
            match uu____28801 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4259_28826 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4259_28826.attempting);
              wl_deferred = (uu___4259_28826.wl_deferred);
              wl_deferred_to_tac = (uu___4259_28826.wl_deferred_to_tac);
              ctr = (uu___4259_28826.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4259_28826.umax_heuristic_ok);
              tcenv = (uu___4259_28826.tcenv);
              wl_implicits = (uu___4259_28826.wl_implicits);
              repr_subcomp_allowed = (uu___4259_28826.repr_subcomp_allowed)
            } in
          (let uu____28828 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____28828
           then
             let uu____28829 = FStar_Util.string_of_bool defer_ok in
             let uu____28830 = wl_to_string wl in
             let uu____28831 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____28829 uu____28830 uu____28831
           else ());
          (let g1 =
             let uu____28834 = solve_and_commit env wl fail in
             match uu____28834 with
             | FStar_Pervasives_Native.Some
                 (uu____28843::uu____28844, uu____28845, uu____28846) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4276_28876 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4276_28876.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4276_28876.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____28881 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____28893 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____28893
             then
               let uu____28894 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____28894
             else ());
            (let uu___4284_28896 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4284_28896.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4284_28896.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4284_28896.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4284_28896.FStar_TypeChecker_Common.implicits)
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
          (let uu____28971 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____28971
           then
             let uu____28972 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____28972
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4301_28976 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4301_28976.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4301_28976.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4301_28976.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4301_28976.FStar_TypeChecker_Common.implicits)
             } in
           let uu____28977 =
             let uu____28978 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____28978 in
           if uu____28977
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____28986 = FStar_TypeChecker_Env.get_range env in
                      let uu____28987 =
                        let uu____28988 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____28988 in
                      FStar_Errors.diag uu____28986 uu____28987)
                   else ();
                   (let vc1 =
                      let uu____28991 =
                        let uu____28994 =
                          let uu____28995 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____28995 in
                        FStar_Pervasives_Native.Some uu____28994 in
                      FStar_Profiling.profile
                        (fun uu____28997 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____28991 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____28999 = FStar_TypeChecker_Env.get_range env in
                       let uu____29000 =
                         let uu____29001 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____29001 in
                       FStar_Errors.diag uu____28999 uu____29000)
                    else ();
                    (let uu____29004 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____29004 "discharge_guard'" env vc1);
                    (let uu____29005 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____29005 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____29012 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____29013 =
                                 let uu____29014 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____29014 in
                               FStar_Errors.diag uu____29012 uu____29013)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____29019 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____29020 =
                                 let uu____29021 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____29021 in
                               FStar_Errors.diag uu____29019 uu____29020)
                            else ();
                            (let vcs =
                               let uu____29032 = FStar_Options.use_tactics () in
                               if uu____29032
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____29052 ->
                                      (let uu____29054 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____29055 -> ()) uu____29054);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____29098 ->
                                               match uu____29098 with
                                               | (env1, goal, opts) ->
                                                   let uu____29114 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____29114, opts)))))
                               else
                                 (let uu____29116 =
                                    let uu____29123 = FStar_Options.peek () in
                                    (env, vc2, uu____29123) in
                                  [uu____29116]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____29156 ->
                                     match uu____29156 with
                                     | (env1, goal, opts) ->
                                         let uu____29166 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____29166 with
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
                                                 (let uu____29173 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____29174 =
                                                    let uu____29175 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____29176 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____29175 uu____29176 in
                                                  FStar_Errors.diag
                                                    uu____29173 uu____29174)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____29179 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____29180 =
                                                    let uu____29181 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____29181 in
                                                  FStar_Errors.diag
                                                    uu____29179 uu____29180)
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
      let uu____29195 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____29195 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____29202 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29202
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____29213 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____29213 with
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
        let uu____29239 = try_teq false env t1 t2 in
        match uu____29239 with
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
             let uu____29282 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____29282 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____29292 =
                   let uu____29293 = FStar_Syntax_Subst.compress t_norm in
                   uu____29293.FStar_Syntax_Syntax.n in
                 (match uu____29292 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____29299 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29299
                        (fun uu____29302 ->
                           FStar_Pervasives_Native.Some uu____29302)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____29304) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____29309 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29309
                        (fun uu____29312 ->
                           FStar_Pervasives_Native.Some uu____29312)
                  | uu____29313 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____29323 =
                      let uu____29324 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____29324 FStar_Util.is_none in
                    if uu____29323
                    then
                      let uu____29329 = imp_value imp in
                      match uu____29329 with
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
        let uu____29350 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____29350 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____29368 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____29368 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____29372 ->
                       let uu____29373 =
                         let uu____29374 = FStar_Syntax_Subst.compress r in
                         uu____29374.FStar_Syntax_Syntax.n in
                       (match uu____29373 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____29378)
                            -> unresolved ctx_u'
                        | uu____29395 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____29415 = acc in
              match uu____29415 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____29422 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____29422 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____29435 = hd in
                       (match uu____29435 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____29441 = unresolved ctx_u in
                               if uu____29441
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____29450 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____29450
                                       then
                                         let uu____29451 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____29451
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____29457 =
                                           teq_nosmt env1 t tm in
                                         match uu____29457 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4446_29466 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4446_29466.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4446_29466.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4446_29466.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4446_29466.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4446_29466.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4446_29466.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4446_29466.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4449_29468 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4449_29468.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4449_29468.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4449_29468.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____29469 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4454_29475 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4454_29475.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4454_29475.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4454_29475.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4454_29475.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4454_29475.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4454_29475.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4454_29475.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4454_29475.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4454_29475.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4454_29475.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4454_29475.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4454_29475.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4454_29475.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4454_29475.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4454_29475.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4454_29475.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4454_29475.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4454_29475.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4454_29475.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4454_29475.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4454_29475.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4454_29475.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4454_29475.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4454_29475.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4454_29475.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4454_29475.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4454_29475.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4454_29475.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4454_29475.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4454_29475.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4454_29475.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4454_29475.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4454_29475.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4454_29475.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4454_29475.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4454_29475.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4454_29475.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4459_29478 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4459_29478.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4459_29478.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4459_29478.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4459_29478.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4459_29478.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4459_29478.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4459_29478.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4459_29478.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4459_29478.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4459_29478.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4459_29478.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4459_29478.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4459_29478.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4459_29478.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4459_29478.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4459_29478.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4459_29478.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4459_29478.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4459_29478.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4459_29478.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4459_29478.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4459_29478.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4459_29478.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4459_29478.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4459_29478.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4459_29478.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4459_29478.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4459_29478.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4459_29478.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4459_29478.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4459_29478.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4459_29478.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____29481 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29481
                                     then
                                       let uu____29482 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____29483 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____29484 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____29485 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____29482 uu____29483 uu____29484
                                         reason uu____29485
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4465_29489 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____29496 =
                                               let uu____29505 =
                                                 let uu____29512 =
                                                   let uu____29513 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____29514 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____29515 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____29513 uu____29514
                                                     uu____29515 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____29512, r) in
                                               [uu____29505] in
                                             FStar_Errors.add_errors
                                               uu____29496);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____29529 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____29539 ->
                                                 let uu____29540 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____29541 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____29542 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____29540 uu____29541
                                                   reason uu____29542)) env2
                                           g1 true in
                                       match uu____29529 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4477_29544 = g in
            let uu____29545 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4477_29544.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4477_29544.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4477_29544.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4477_29544.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____29545
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____29557 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29557
       then
         let uu____29558 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____29558
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
      (let uu____29581 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29581
       then
         let uu____29582 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____29582
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____29586 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____29587 -> ()) uu____29586
       | imp::uu____29589 ->
           let uu____29592 =
             let uu____29597 =
               let uu____29598 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____29599 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____29598 uu____29599
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29597) in
           FStar_Errors.raise_error uu____29592
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29615 = teq env t1 t2 in
        force_trivial_guard env uu____29615
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29631 = teq_nosmt env t1 t2 in
        match uu____29631 with
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
          (let uu____29661 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____29661
           then
             let uu____29662 =
               let uu____29663 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____29663
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____29669 = FStar_Syntax_Print.term_to_string t1 in
             let uu____29670 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____29662
               uu____29669 uu____29670
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4515_29682 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4515_29682.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4515_29682.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4515_29682.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4515_29682.FStar_TypeChecker_Common.implicits)
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
        (let uu____29717 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29717
         then
           let uu____29718 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29719 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29718
             uu____29719
         else ());
        (let uu____29721 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29721 with
         | (prob, x, wl) ->
             let g =
               let uu____29740 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29750 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29740 in
             ((let uu____29772 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____29772
               then
                 let uu____29773 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____29774 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____29775 =
                   let uu____29776 = FStar_Util.must g in
                   guard_to_string env uu____29776 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29773 uu____29774 uu____29775
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
        let uu____29810 = check_subtyping env t1 t2 in
        match uu____29810 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29829 =
              let uu____29830 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____29830 g in
            FStar_Pervasives_Native.Some uu____29829
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29848 = check_subtyping env t1 t2 in
        match uu____29848 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29867 =
              let uu____29868 =
                let uu____29869 = FStar_Syntax_Syntax.mk_binder x in
                [uu____29869] in
              FStar_TypeChecker_Env.close_guard env uu____29868 g in
            FStar_Pervasives_Native.Some uu____29867
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____29906 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29906
         then
           let uu____29907 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29908 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____29907
             uu____29908
         else ());
        (let uu____29910 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29910 with
         | (prob, x, wl) ->
             let g =
               let uu____29925 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____29935 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29925 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____29960 =
                      let uu____29961 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____29961] in
                    FStar_TypeChecker_Env.close_guard env uu____29960 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29998 = subtype_nosmt env t1 t2 in
        match uu____29998 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)