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
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt ->
    fun src ->
      fun wl ->
        let uu____5817 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders in
        match uu____5817 with
        | (pfx, uu____5827) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx in
            let uu____5839 =
              let uu____5846 =
                let uu____5847 =
                  FStar_Syntax_Print.uvar_to_string
                    src.FStar_Syntax_Syntax.ctx_uvar_head in
                Prims.op_Hat "restricted " uu____5847 in
              new_uvar uu____5846 wl src.FStar_Syntax_Syntax.ctx_uvar_range g
                pfx src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta in
            (match uu____5839 with
             | (uu____5848, src', wl1) ->
                 (FStar_Syntax_Util.set_uvar
                    src.FStar_Syntax_Syntax.ctx_uvar_head src';
                  wl1))
let (restrict_all_uvars :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun tgt ->
    fun sources ->
      fun wl -> FStar_List.fold_right (restrict_ctx tgt) sources wl
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
                 | uu____5960 -> out) FStar_Syntax_Syntax.no_names g in
        let uu____5961 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6025 ->
                  fun uu____6026 ->
                    match (uu____6025, uu____6026) with
                    | ((isect, isect_set), (x, imp)) ->
                        let uu____6129 =
                          let uu____6130 = FStar_Util.set_mem x v1_set in
                          FStar_All.pipe_left Prims.op_Negation uu____6130 in
                        if uu____6129
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6159 =
                             FStar_Util.set_is_subset_of fvs isect_set in
                           if uu____6159
                           then
                             let uu____6174 = FStar_Util.set_add x isect_set in
                             (((x, imp) :: isect), uu____6174)
                           else (isect, isect_set))) ([], ctx_binders)) in
        match uu____5961 with | (isect, uu____6223) -> FStar_List.rev isect
let binders_eq :
  'uuuuuu6258 'uuuuuu6259 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6258) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6259) Prims.list -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6316 ->
              fun uu____6317 ->
                match (uu____6316, uu____6317) with
                | ((a, uu____6335), (b, uu____6337)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let name_exists_in_binders :
  'uuuuuu6352 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6352) Prims.list -> Prims.bool
  =
  fun x ->
    fun bs ->
      FStar_Util.for_some
        (fun uu____6382 ->
           match uu____6382 with
           | (y, uu____6388) -> FStar_Syntax_Syntax.bv_eq x y) bs
let pat_vars :
  'uuuuuu6397 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6397) Prims.list ->
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
                   let uu____6559 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu____6559
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6589 -> FStar_Pervasives_Native.None) in
        aux [] args
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu____6636 -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch _0 -> true | uu____6673 -> false
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee -> match projectee with | HeadMatch _0 -> _0
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | FullMatch -> true | uu____6685 -> false
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_6690 ->
    match uu___19_6690 with
    | MisMatch (d1, d2) ->
        let uu____6701 =
          let uu____6702 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu____6703 =
            let uu____6704 =
              let uu____6705 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.op_Hat uu____6705 ")" in
            Prims.op_Hat ") (" uu____6704 in
          Prims.op_Hat uu____6702 uu____6703 in
        Prims.op_Hat "MisMatch (" uu____6701
    | HeadMatch u ->
        let uu____6707 = FStar_Util.string_of_bool u in
        Prims.op_Hat "HeadMatch " uu____6707
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___20_6712 ->
    match uu___20_6712 with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu____6727 -> HeadMatch false
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____6740 =
            (let uu____6745 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
             let uu____6746 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu____6745 = uu____6746) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) in
          if uu____6740 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____6749 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6749 with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6760 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6783 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6792 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6810 = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu____6810
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6811 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6812 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6813 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6826 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6839 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____6863) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____6869, uu____6870) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu____6912) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6937;
             FStar_Syntax_Syntax.index = uu____6938;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____6940)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6947 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6948 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6949 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6964 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6971 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6991 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____6991
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
           { FStar_Syntax_Syntax.blob = uu____7009;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7010;
             FStar_Syntax_Syntax.ltyp = uu____7011;
             FStar_Syntax_Syntax.rng = uu____7012;_},
           uu____7013) ->
            let uu____7024 = FStar_Syntax_Util.unlazy t11 in
            head_matches env uu____7024 t21
        | (uu____7025, FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7026;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7027;
             FStar_Syntax_Syntax.ltyp = uu____7028;
             FStar_Syntax_Syntax.rng = uu____7029;_})
            ->
            let uu____7040 = FStar_Syntax_Util.unlazy t21 in
            head_matches env t11 uu____7040
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7043 = FStar_Syntax_Syntax.bv_eq x y in
            if uu____7043
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7051 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____7051
            then FullMatch
            else
              (let uu____7053 =
                 let uu____7062 =
                   let uu____7065 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____7065 in
                 let uu____7066 =
                   let uu____7069 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____7069 in
                 (uu____7062, uu____7066) in
               MisMatch uu____7053)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu____7075),
           FStar_Syntax_Syntax.Tm_uinst (g, uu____7077)) ->
            let uu____7086 = head_matches env f g in
            FStar_All.pipe_right uu____7086 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           uu____7087) -> HeadMatch true
        | (uu____7088, FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify)) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7091 = FStar_Const.eq_const c d in
            if uu____7091
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu____7098),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu____7100)) ->
            let uu____7133 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head in
            if uu____7133
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7140),
           FStar_Syntax_Syntax.Tm_refine (y, uu____7142)) ->
            let uu____7151 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7151 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7153), uu____7154) ->
            let uu____7159 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____7159 head_match
        | (uu____7160, FStar_Syntax_Syntax.Tm_refine (x, uu____7162)) ->
            let uu____7167 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7167 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7168,
           FStar_Syntax_Syntax.Tm_type uu____7169) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow uu____7170,
           FStar_Syntax_Syntax.Tm_arrow uu____7171) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7201),
           FStar_Syntax_Syntax.Tm_app (head', uu____7203)) ->
            let uu____7252 = head_matches env head head' in
            FStar_All.pipe_right uu____7252 head_match
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7254), uu____7255) ->
            let uu____7280 = head_matches env head t21 in
            FStar_All.pipe_right uu____7280 head_match
        | (uu____7281, FStar_Syntax_Syntax.Tm_app (head, uu____7283)) ->
            let uu____7308 = head_matches env t11 head in
            FStar_All.pipe_right uu____7308 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7309, FStar_Syntax_Syntax.Tm_let
           uu____7310) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match uu____7335,
           FStar_Syntax_Syntax.Tm_match uu____7336) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7381, FStar_Syntax_Syntax.Tm_abs
           uu____7382) -> HeadMatch true
        | uu____7419 ->
            let uu____7424 =
              let uu____7433 = delta_depth_of_term env t11 in
              let uu____7436 = delta_depth_of_term env t21 in
              (uu____7433, uu____7436) in
            MisMatch uu____7424
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
              let uu____7504 = unrefine env t in
              FStar_Syntax_Util.head_of uu____7504 in
            (let uu____7506 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7506
             then
               let uu____7507 = FStar_Syntax_Print.term_to_string t in
               let uu____7508 = FStar_Syntax_Print.term_to_string head in
               FStar_Util.print2 "Head of %s is %s\n" uu____7507 uu____7508
             else ());
            (let uu____7510 =
               let uu____7511 = FStar_Syntax_Util.un_uinst head in
               uu____7511.FStar_Syntax_Syntax.n in
             match uu____7510 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7517 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 (match uu____7517 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu____7531 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta") in
                        if uu____7531
                        then
                          let uu____7532 =
                            FStar_Syntax_Print.term_to_string head in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7532
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7534 ->
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
                      let uu____7549 =
                        let uu____7550 = FStar_Syntax_Util.eq_tm t t' in
                        uu____7550 = FStar_Syntax_Util.Equal in
                      if uu____7549
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7555 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta") in
                          if uu____7555
                          then
                            let uu____7556 =
                              FStar_Syntax_Print.term_to_string t in
                            let uu____7557 =
                              FStar_Syntax_Print.term_to_string t' in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7556
                              uu____7557
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7559 -> FStar_Pervasives_Native.None) in
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
            (let uu____7697 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7697
             then
               let uu____7698 = FStar_Syntax_Print.term_to_string t11 in
               let uu____7699 = FStar_Syntax_Print.term_to_string t21 in
               let uu____7700 = string_of_match_result r in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7698
                 uu____7699 uu____7700
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
               let uu____7724 =
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
               match uu____7724 with
               | (t12, t22) -> aux retry (n_delta + Prims.int_one) t12 t22 in
             let reduce_both_and_try_again d r1 =
               let uu____7769 = FStar_TypeChecker_Common.decr_delta_depth d in
               match uu____7769 with
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
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7801),
                  uu____7802)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____7820 =
                      let uu____7829 = maybe_inline t11 in
                      let uu____7832 = maybe_inline t21 in
                      (uu____7829, uu____7832) in
                    match uu____7820 with
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
                 (uu____7869, FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7870))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____7888 =
                      let uu____7897 = maybe_inline t11 in
                      let uu____7900 = maybe_inline t21 in
                      (uu____7897, uu____7900) in
                    match uu____7888 with
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
             | MisMatch uu____7949 -> fail n_delta r t11 t21
             | uu____7958 -> success n_delta r t11 t21) in
          let r = aux true Prims.int_zero t1 t2 in
          (let uu____7971 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu____7971
           then
             let uu____7972 = FStar_Syntax_Print.term_to_string t1 in
             let uu____7973 = FStar_Syntax_Print.term_to_string t2 in
             let uu____7974 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             let uu____7981 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____7993 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must in
                  FStar_All.pipe_right uu____7993
                    (fun uu____8027 ->
                       match uu____8027 with
                       | (t11, t21) ->
                           let uu____8034 =
                             FStar_Syntax_Print.term_to_string t11 in
                           let uu____8035 =
                             let uu____8036 =
                               FStar_Syntax_Print.term_to_string t21 in
                             Prims.op_Hat "; " uu____8036 in
                           Prims.op_Hat uu____8034 uu____8035)) in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7972 uu____7973 uu____7974 uu____7981
           else ());
          r
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____8048 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____8048 FStar_Pervasives_Native.fst
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8061 ->
    match uu___21_8061 with
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
      let uu___1259_8098 = p in
      let uu____8101 = whnf tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8102 = whnf tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1259_8098.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8101;
        FStar_TypeChecker_Common.relation =
          (uu___1259_8098.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8102;
        FStar_TypeChecker_Common.element =
          (uu___1259_8098.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1259_8098.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1259_8098.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1259_8098.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1259_8098.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1259_8098.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8116 = compress_tprob tcenv p1 in
          FStar_All.pipe_right uu____8116
            (fun uu____8121 -> FStar_TypeChecker_Common.TProb uu____8121)
      | FStar_TypeChecker_Common.CProb uu____8122 -> p
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv ->
    fun pr ->
      let prob =
        let uu____8144 = compress_prob tcenv pr in
        FStar_All.pipe_right uu____8144 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8152 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8152 with
           | (lh, lhs_args) ->
               let uu____8199 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8199 with
                | (rh, rhs_args) ->
                    let uu____8246 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8259,
                         FStar_Syntax_Syntax.Tm_uvar uu____8260) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8349 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8376, uu____8377)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8392, FStar_Syntax_Syntax.Tm_uvar uu____8393)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8408,
                         FStar_Syntax_Syntax.Tm_arrow uu____8409) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_8439 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_8439.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_8439.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_8439.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_8439.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_8439.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_8439.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_8439.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_8439.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_8439.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8442,
                         FStar_Syntax_Syntax.Tm_type uu____8443) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_8459 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_8459.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_8459.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_8459.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_8459.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_8459.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_8459.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_8459.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_8459.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_8459.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type uu____8462,
                         FStar_Syntax_Syntax.Tm_uvar uu____8463) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_8479 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_8479.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_8479.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_8479.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_8479.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_8479.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_8479.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_8479.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_8479.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_8479.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8482, FStar_Syntax_Syntax.Tm_uvar uu____8483)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8498, uu____8499)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8514, FStar_Syntax_Syntax.Tm_uvar uu____8515)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8530, uu____8531) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu____8246 with
                     | (rank, tp1) ->
                         let uu____8544 =
                           FStar_All.pipe_right
                             (let uu___1330_8548 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1330_8548.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1330_8548.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1330_8548.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1330_8548.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1330_8548.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1330_8548.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1330_8548.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1330_8548.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1330_8548.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____8551 ->
                                FStar_TypeChecker_Common.TProb uu____8551) in
                         (rank, uu____8544))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8555 =
            FStar_All.pipe_right
              (let uu___1334_8559 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1334_8559.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1334_8559.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1334_8559.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1334_8559.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1334_8559.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1334_8559.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1334_8559.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1334_8559.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1334_8559.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____8562 -> FStar_TypeChecker_Common.CProb uu____8562) in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8555)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    let rec aux uu____8621 probs =
      match uu____8621 with
      | (min_rank, min, out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some p,
                   FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8702 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____8723 = rank wl.tcenv hd in
               (match uu____8723 with
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
                      (let uu____8782 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8786 = FStar_Option.get min_rank in
                            rank_less_than rank1 uu____8786) in
                       if uu____8782
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
          let uu____8854 = FStar_Syntax_Util.head_and_args t in
          match uu____8854 with
          | (hd, uu____8872) ->
              let uu____8897 =
                let uu____8898 = FStar_Syntax_Subst.compress hd in
                uu____8898.FStar_Syntax_Syntax.n in
              (match uu____8897 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu____8902) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8936 ->
                           match uu____8936 with
                           | (y, uu____8944) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8966 ->
                                       match uu____8966 with
                                       | (x, uu____8974) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8979 -> false) in
        let uu____8980 = rank tcenv p in
        match uu____8980 with
        | (r, p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8987 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9019 -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | USolved _0 -> true | uu____9032 -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UFailed _0 -> true | uu____9045 -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s -> let uu____9057 = FStar_Thunk.mkv s in UFailed uu____9057
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu____9068 = mklstr s in UFailed uu____9068
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
                        let uu____9113 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____9113 with
                        | (k, uu____9119) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9131 -> false)))
            | uu____9132 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu____9184 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2 -> FStar_Syntax_Util.eq_univs uv1 uv2)) in
                        if uu____9184 then uv1 :: uvs else uvs) []) in
            let filter =
              FStar_List.filter
                (fun u ->
                   let uu____9204 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u' -> FStar_Syntax_Util.eq_univs u u')) in
                   Prims.op_Negation uu____9204) in
            let uu____9209 = filter u12 in
            let uu____9212 = filter u22 in (uu____9209, uu____9212) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9242 = filter_out_common_univs us1 us2 in
                   (match uu____9242 with
                    | (us11, us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13, u23::us23) ->
                                let uu____9301 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23 in
                                (match uu____9301 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9304 -> USolved wl1 in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9320 ->
                               let uu____9321 =
                                 FStar_Syntax_Print.univ_to_string u12 in
                               let uu____9322 =
                                 FStar_Syntax_Print.univ_to_string u22 in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9321 uu____9322))
               | (FStar_Syntax_Syntax.U_max us, u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9346 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9346 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | (u', FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9372 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9372 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | uu____9375 ->
                   ufailed_thunk
                     (fun uu____9386 ->
                        let uu____9387 =
                          FStar_Syntax_Print.univ_to_string u12 in
                        let uu____9388 =
                          FStar_Syntax_Print.univ_to_string u22 in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____9387 uu____9388 msg)) in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9389, uu____9390) ->
              let uu____9391 =
                let uu____9392 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9393 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9392 uu____9393 in
              failwith uu____9391
          | (FStar_Syntax_Syntax.U_unknown, uu____9394) ->
              let uu____9395 =
                let uu____9396 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9397 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9396 uu____9397 in
              failwith uu____9395
          | (uu____9398, FStar_Syntax_Syntax.U_bvar uu____9399) ->
              let uu____9400 =
                let uu____9401 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9402 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9401 uu____9402 in
              failwith uu____9400
          | (uu____9403, FStar_Syntax_Syntax.U_unknown) ->
              let uu____9404 =
                let uu____9405 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9406 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9405 uu____9406 in
              failwith uu____9404
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              let uu____9409 =
                let uu____9410 = FStar_Ident.string_of_id x in
                let uu____9411 = FStar_Ident.string_of_id y in
                uu____9410 = uu____9411 in
              if uu____9409
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9437 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9437
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu____9453 = occurs_univ v1 u3 in
              if uu____9453
              then
                let uu____9454 =
                  let uu____9455 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9456 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9455 uu____9456 in
                try_umax_components u11 u21 uu____9454
              else
                (let uu____9458 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9458)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9472 = occurs_univ v1 u3 in
              if uu____9472
              then
                let uu____9473 =
                  let uu____9474 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9475 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9474 uu____9475 in
                try_umax_components u11 u21 uu____9473
              else
                (let uu____9477 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9477)
          | (FStar_Syntax_Syntax.U_max uu____9478, uu____9479) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9485 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9485
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9487, FStar_Syntax_Syntax.U_max uu____9488) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9494 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9494
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9496,
             FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9497,
             FStar_Syntax_Syntax.U_name uu____9498) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ
             uu____9499) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name
             uu____9500) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9501,
             FStar_Syntax_Syntax.U_succ uu____9502) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9503,
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
      let uu____9603 = bc1 in
      match uu____9603 with
      | (bs1, mk_cod1) ->
          let uu____9647 = bc2 in
          (match uu____9647 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu____9758 = aux xs ys in
                     (match uu____9758 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu____9841 =
                       let uu____9848 = mk_cod1 xs in ([], uu____9848) in
                     let uu____9851 =
                       let uu____9858 = mk_cod2 ys in ([], uu____9858) in
                     (uu____9841, uu____9851) in
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
                  let uu____9926 = FStar_Syntax_Syntax.bv_to_name t in
                  FStar_Syntax_Util.mk_has_type t11 uu____9926 t21
              | FStar_Pervasives_Native.None ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11 in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11 in
                  let uu____9929 =
                    let uu____9930 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Util.mk_has_type t11 uu____9930 t21 in
                  FStar_Syntax_Util.mk_forall u_x x uu____9929 in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB ->
                let uu____9935 = has_type_guard t1 t2 in (uu____9935, wl)
            | FStar_TypeChecker_Common.SUBINV ->
                let uu____9936 = has_type_guard t2 t1 in (uu____9936, wl)
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_9941 ->
    match uu___22_9941 with
    | Flex (uu____9942, uu____9943, []) -> true
    | uu____9952 -> false
let (should_defer_flex_to_user_tac :
  FStar_TypeChecker_Env.env -> worklist -> flex_t -> Prims.bool) =
  fun env ->
    fun wl ->
      fun f ->
        let uu____9968 = f in
        match uu____9968 with
        | Flex (uu____9969, u, uu____9971) ->
            let b =
              FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                wl.tcenv u in
            ((let uu____9974 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ResolveImplicitsHook") in
              if uu____9974
              then
                let uu____9975 =
                  FStar_Syntax_Print.ctx_uvar_to_string_no_reason u in
                let uu____9976 = FStar_Util.string_of_bool b in
                FStar_Util.print2
                  "Rel.should_defer_flex_to_user_tac for %s returning %s\n"
                  uu____9975 uu____9976
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
      let uu____10000 = f in
      match uu____10000 with
      | Flex
          (uu____10007,
           { FStar_Syntax_Syntax.ctx_uvar_head = uu____10008;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10009;
             FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
             FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____10012;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____10013;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____10014;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____10015;_},
           args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10079 ->
                 match uu____10079 with
                 | (y, uu____10087) -> FStar_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu____10241 =
                  let uu____10256 =
                    let uu____10259 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10259 in
                  ((FStar_List.rev pat_binders), uu____10256) in
                FStar_Pervasives_Native.Some uu____10241
            | (uu____10292, []) ->
                let uu____10323 =
                  let uu____10338 =
                    let uu____10341 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10341 in
                  ((FStar_List.rev pat_binders), uu____10338) in
                FStar_Pervasives_Native.Some uu____10323
            | ((formal, formal_imp)::formals1, (a, a_imp)::args2) ->
                let uu____10432 =
                  let uu____10433 = FStar_Syntax_Subst.compress a in
                  uu____10433.FStar_Syntax_Syntax.n in
                (match uu____10432 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____10453 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders) in
                     if uu____10453
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1675_10480 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1675_10480.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1675_10480.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          } in
                        let subst =
                          let uu____10484 =
                            let uu____10485 =
                              let uu____10492 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              (formal, uu____10492) in
                            FStar_Syntax_Syntax.NT uu____10485 in
                          [uu____10484] in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1 in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res in
                        aux
                          (((let uu___1681_10508 = x1 in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1681_10508.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1681_10508.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10509 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([], args2) ->
                let uu____10549 =
                  let uu____10556 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStar_Syntax_Util.arrow_formals uu____10556 in
                (match uu____10549 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10615 ->
                          aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10640 ->
               let uu____10641 = FStar_Syntax_Util.arrow_formals t_hd in
               (match uu____10641 with
                | (formals, t_res) -> aux [] formals t_res args))
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu____10970 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel") in
       if uu____10970
       then
         let uu____10971 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10971
       else ());
      (let uu____10974 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace") in
       if uu____10974
       then
         let uu____10975 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____10975
       else ());
      (let uu____10977 = next_prob probs in
       match uu____10977 with
       | FStar_Pervasives_Native.Some (hd, tl, rank1) ->
           let probs1 =
             let uu___1708_11004 = probs in
             {
               attempting = tl;
               wl_deferred = (uu___1708_11004.wl_deferred);
               wl_deferred_to_tac = (uu___1708_11004.wl_deferred_to_tac);
               ctr = (uu___1708_11004.ctr);
               defer_ok = (uu___1708_11004.defer_ok);
               smt_ok = (uu___1708_11004.smt_ok);
               umax_heuristic_ok = (uu___1708_11004.umax_heuristic_ok);
               tcenv = (uu___1708_11004.tcenv);
               wl_implicits = (uu___1708_11004.wl_implicits);
               repr_subcomp_allowed = (uu___1708_11004.repr_subcomp_allowed)
             } in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11012 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs in
                 if uu____11012
                 then
                   let uu____11013 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                   solve env uu____11013
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
                           (let uu___1720_11018 = tp in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1720_11018.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1720_11018.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1720_11018.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1720_11018.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1720_11018.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1720_11018.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1720_11018.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1720_11018.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1720_11018.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None ->
           (match probs.wl_deferred with
            | [] ->
                let uu____11036 =
                  let uu____11043 = as_deferred probs.wl_deferred_to_tac in
                  ([], uu____11043, (probs.wl_implicits)) in
                Success uu____11036
            | uu____11048 ->
                let uu____11057 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11116 ->
                          match uu____11116 with
                          | (c, uu____11124, uu____11125) -> c < probs.ctr)) in
                (match uu____11057 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11166 =
                            let uu____11173 = as_deferred probs.wl_deferred in
                            let uu____11174 =
                              as_deferred probs.wl_deferred_to_tac in
                            (uu____11173, uu____11174, (probs.wl_implicits)) in
                          Success uu____11166
                      | uu____11175 ->
                          let uu____11184 =
                            let uu___1734_11185 = probs in
                            let uu____11186 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11205 ->
                                      match uu____11205 with
                                      | (uu____11212, uu____11213, y) -> y)) in
                            {
                              attempting = uu____11186;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1734_11185.wl_deferred_to_tac);
                              ctr = (uu___1734_11185.ctr);
                              defer_ok = (uu___1734_11185.defer_ok);
                              smt_ok = (uu___1734_11185.smt_ok);
                              umax_heuristic_ok =
                                (uu___1734_11185.umax_heuristic_ok);
                              tcenv = (uu___1734_11185.tcenv);
                              wl_implicits = (uu___1734_11185.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1734_11185.repr_subcomp_allowed)
                            } in
                          solve env uu____11184))))
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
            let uu____11220 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____11220 with
            | USolved wl1 ->
                let uu____11222 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____11222
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11225 = defer_lit "" orig wl1 in
                solve env uu____11225
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
                  let uu____11275 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____11275 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11278 -> ufailed_simple "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11290;
                  FStar_Syntax_Syntax.vars = uu____11291;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11294;
                  FStar_Syntax_Syntax.vars = uu____11295;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11307, uu____11308) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11315, FStar_Syntax_Syntax.Tm_uinst uu____11316) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11323 -> USolved wl
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
            ((let uu____11333 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____11333
              then
                let uu____11334 = prob_to_string env orig in
                let uu____11335 = FStar_Thunk.force msg in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11334 uu____11335
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
          (let uu____11343 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____11343
           then
             let uu____11344 = prob_to_string env orig in
             FStar_Util.print1 "\n\t\tDeferring %s to a tactic\n" uu____11344
           else ());
          (let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
           let wl2 =
             let uu___1818_11348 = wl1 in
             let uu____11349 =
               let uu____11358 =
                 let uu____11365 = FStar_Thunk.mkv reason in
                 ((wl1.ctr), uu____11365, orig) in
               uu____11358 :: (wl1.wl_deferred_to_tac) in
             {
               attempting = (uu___1818_11348.attempting);
               wl_deferred = (uu___1818_11348.wl_deferred);
               wl_deferred_to_tac = uu____11349;
               ctr = (uu___1818_11348.ctr);
               defer_ok = (uu___1818_11348.defer_ok);
               smt_ok = (uu___1818_11348.smt_ok);
               umax_heuristic_ok = (uu___1818_11348.umax_heuristic_ok);
               tcenv = (uu___1818_11348.tcenv);
               wl_implicits = (uu___1818_11348.wl_implicits);
               repr_subcomp_allowed = (uu___1818_11348.repr_subcomp_allowed)
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
                let uu____11388 = FStar_Syntax_Util.head_and_args t in
                match uu____11388 with
                | (head, uu____11410) ->
                    let uu____11435 =
                      let uu____11436 = FStar_Syntax_Subst.compress head in
                      uu____11436.FStar_Syntax_Syntax.n in
                    (match uu____11435 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu____11444) ->
                         let uu____11461 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu____11461,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____11462 -> (false, "")) in
              let uu____11463 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu____11463 with
               | (l1, r1) ->
                   let uu____11470 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu____11470 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____11478 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl in
                           solve env uu____11478)))
          | uu____11479 ->
              let uu____11480 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu____11480
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
               let uu____11564 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu____11564 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu____11617 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu____11617
                then
                  let uu____11618 = FStar_Syntax_Print.term_to_string t1 in
                  let uu____11619 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____11618 uu____11619
                else ());
               (let uu____11621 = head_matches_delta env1 wl2 t1 t2 in
                match uu____11621 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu____11666 = eq_prob t1 t2 wl2 in
                         (match uu____11666 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11687 ->
                         let uu____11696 = eq_prob t1 t2 wl2 in
                         (match uu____11696 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu____11745 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu____11760 =
                                 FStar_Syntax_Subst.compress t11 in
                               let uu____11761 =
                                 FStar_Syntax_Subst.compress t21 in
                               (uu____11760, uu____11761)
                           | FStar_Pervasives_Native.None ->
                               let uu____11766 =
                                 FStar_Syntax_Subst.compress t1 in
                               let uu____11767 =
                                 FStar_Syntax_Subst.compress t2 in
                               (uu____11766, uu____11767) in
                         (match uu____11745 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11798 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu____11798 with
                                | (t1_hd, t1_args) ->
                                    let uu____11843 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu____11843 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11907 =
                                              let uu____11914 =
                                                let uu____11925 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu____11925 :: t1_args in
                                              let uu____11942 =
                                                let uu____11951 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu____11951 :: t2_args in
                                              FStar_List.fold_left2
                                                (fun uu____12000 ->
                                                   fun uu____12001 ->
                                                     fun uu____12002 ->
                                                       match (uu____12000,
                                                               uu____12001,
                                                               uu____12002)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu____12052),
                                                          (a2, uu____12054))
                                                           ->
                                                           let uu____12091 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu____12091
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11914
                                                uu____11942 in
                                            match uu____11907 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  let uu___1921_12117 = wl4 in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1921_12117.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1921_12117.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1921_12117.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1921_12117.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1921_12117.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____12125 =
                                                  solve env1 wl' in
                                                (match uu____12125 with
                                                 | Success
                                                     (uu____12128,
                                                      defer_to_tac, imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____12132 =
                                                         extend_wl wl4
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu____12132))
                                                 | Failed uu____12133 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu____12165 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu____12165 with
                                | (t1_base, p1_opt) ->
                                    let uu____12200 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu____12200 with
                                     | (t2_base, p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____12298 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu____12298
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
                                               let uu____12346 =
                                                 op phi11 phi21 in
                                               refine x1 uu____12346
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
                                               let uu____12376 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12376
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
                                               let uu____12406 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12406
                                           | uu____12409 -> t_base in
                                         let uu____12426 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu____12426 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____12440 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu____12440, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu____12447 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu____12447 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu____12482 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu____12482 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu____12517 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu____12517
                                                         with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu____12541 = combine t11 t21 wl2 in
                              (match uu____12541 with
                               | (t12, ps, wl3) ->
                                   ((let uu____12574 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu____12574
                                     then
                                       let uu____12575 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____12575
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu____12614 ts1 =
               match uu____12614 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12677 = pairwise out t wl2 in
                        (match uu____12677 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2)) in
             let uu____12713 =
               let uu____12724 = FStar_List.hd ts in (uu____12724, [], wl1) in
             let uu____12733 = FStar_List.tl ts in
             aux uu____12713 uu____12733 in
           let uu____12740 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu____12740 with
           | (this_flex, this_rigid) ->
               let uu____12764 =
                 let uu____12765 = FStar_Syntax_Subst.compress this_rigid in
                 uu____12765.FStar_Syntax_Syntax.n in
               (match uu____12764 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu____12790 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu____12790
                    then
                      let uu____12791 = destruct_flex_t this_flex wl in
                      (match uu____12791 with
                       | (flex, wl1) ->
                           let uu____12798 = quasi_pattern env flex in
                           (match uu____12798 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu____12816 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____12816
                                  then
                                    let uu____12817 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12817
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12820 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2031_12823 = tp in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2031_12823.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2031_12823.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2031_12823.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2031_12823.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2031_12823.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2031_12823.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2031_12823.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2031_12823.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2031_12823.FStar_TypeChecker_Common.rank)
                                }))] wl in
                       solve env uu____12820)
                | uu____12824 ->
                    ((let uu____12826 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____12826
                      then
                        let uu____12827 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12827
                      else ());
                     (let uu____12829 =
                        FStar_Syntax_Util.head_and_args this_flex in
                      match uu____12829 with
                      | (u, _args) ->
                          let uu____12872 =
                            let uu____12873 = FStar_Syntax_Subst.compress u in
                            uu____12873.FStar_Syntax_Syntax.n in
                          (match uu____12872 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu____12900 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu____12900 with
                                 | (u', uu____12918) ->
                                     let uu____12943 =
                                       let uu____12944 = whnf env u' in
                                       uu____12944.FStar_Syntax_Syntax.n in
                                     (match uu____12943 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12965 -> false) in
                               let uu____12966 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_12989 ->
                                         match uu___23_12989 with
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
                                              | uu____12998 -> false)
                                         | uu____13001 -> false)) in
                               (match uu____12966 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu____13015 = whnf env this_rigid in
                                      let uu____13016 =
                                        FStar_List.collect
                                          (fun uu___24_13022 ->
                                             match uu___24_13022 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13028 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu____13028]
                                             | uu____13030 -> [])
                                          bounds_probs in
                                      uu____13015 :: uu____13016 in
                                    let uu____13031 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu____13031 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu____13062 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu____13077 =
                                               let uu____13078 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu____13078.FStar_Syntax_Syntax.n in
                                             match uu____13077 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13090 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13090)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13099 -> bound in
                                           let uu____13100 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu____13100) in
                                         (match uu____13062 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13129 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu____13129
                                                then
                                                  let wl'1 =
                                                    let uu___2091_13131 = wl1 in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2091_13131.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2091_13131.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2091_13131.ctr);
                                                      defer_ok =
                                                        (uu___2091_13131.defer_ok);
                                                      smt_ok =
                                                        (uu___2091_13131.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2091_13131.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2091_13131.tcenv);
                                                      wl_implicits =
                                                        (uu___2091_13131.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2091_13131.repr_subcomp_allowed)
                                                    } in
                                                  let uu____13132 =
                                                    wl_to_string wl'1 in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13132
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____13135 =
                                                  solve_t env eq_prob
                                                    (let uu___2096_13137 =
                                                       wl' in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2096_13137.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2096_13137.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2096_13137.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2096_13137.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2096_13137.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2096_13137.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2096_13137.repr_subcomp_allowed)
                                                     }) in
                                                match uu____13135 with
                                                | Success
                                                    (uu____13138,
                                                     defer_to_tac, imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2103_13142 =
                                                        wl' in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2103_13142.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2103_13142.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2103_13142.ctr);
                                                        defer_ok =
                                                          (uu___2103_13142.defer_ok);
                                                        smt_ok =
                                                          (uu___2103_13142.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2103_13142.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2103_13142.tcenv);
                                                        wl_implicits =
                                                          (uu___2103_13142.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2103_13142.repr_subcomp_allowed)
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
                                                    let uu____13158 =
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
                                                    ((let uu____13169 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu____13169
                                                      then
                                                        let uu____13170 =
                                                          let uu____13171 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_All.pipe_right
                                                            uu____13171
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13170
                                                      else ());
                                                     (let uu____13177 =
                                                        let uu____13192 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu____13192) in
                                                      match uu____13177 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu____13214)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13240 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13240
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
                                                                  let uu____13257
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13257))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13282 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13282
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
                                                                    let uu____13300
                                                                    =
                                                                    let uu____13305
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13305 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13300
                                                                    [] wl2 in
                                                                  let uu____13310
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13310))))
                                                      | uu____13311 ->
                                                          let uu____13326 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env
                                                            uu____13326 p)))))))
                           | uu____13329 when flip ->
                               let uu____13330 =
                                 let uu____13331 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13332 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13331 uu____13332 in
                               failwith uu____13330
                           | uu____13333 ->
                               let uu____13334 =
                                 let uu____13335 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13336 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13335 uu____13336 in
                               failwith uu____13334)))))
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
                      (fun uu____13370 ->
                         match uu____13370 with
                         | (x, i) ->
                             let uu____13389 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             (uu____13389, i)) bs_lhs in
                  let uu____13392 = lhs in
                  match uu____13392 with
                  | Flex (uu____13393, u_lhs, uu____13395) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____13492 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____13502 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu____13502, univ) in
                          match uu____13492 with
                          | (k, univ) ->
                              let uu____13509 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2 in
                              (match uu____13509 with
                               | (uu____13526, u, wl3) ->
                                   let uu____13529 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu____13529, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____13555 =
                              let uu____13568 =
                                let uu____13579 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu____13579 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_List.fold_right
                                (fun uu____13630 ->
                                   fun uu____13631 ->
                                     match (uu____13630, uu____13631) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu____13732 =
                                           let uu____13739 =
                                             let uu____13742 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13742 in
                                           copy_uvar u_lhs [] uu____13739 wl2 in
                                         (match uu____13732 with
                                          | (uu____13771, t_a, wl3) ->
                                              let uu____13774 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu____13774 with
                                               | (uu____13793, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____13568
                                ([], wl1) in
                            (match uu____13555 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_13862 ->
                                        match uu___25_13862 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____13863 -> false
                                        | uu____13866 -> true) flags in
                                 let ct' =
                                   let uu___2222_13868 = ct in
                                   let uu____13869 =
                                     let uu____13872 = FStar_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu____13872 in
                                   let uu____13887 = FStar_List.tl out_args in
                                   let uu____13904 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2222_13868.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2222_13868.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13869;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13887;
                                     FStar_Syntax_Syntax.flags = uu____13904
                                   } in
                                 ((let uu___2225_13908 = c in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2225_13908.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2225_13908.FStar_Syntax_Syntax.vars)
                                   }), wl2)) in
                      let uu____13911 =
                        FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu____13911 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13949 =
                                   imitate_comp bs bs_terms c wl1 in
                                 (match uu____13949 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu____13960 =
                                          let uu____13965 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____13965) in
                                        TERM uu____13960 in
                                      let uu____13966 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu____13966 with
                                       | (sub_prob, wl3) ->
                                           let uu____13979 =
                                             let uu____13980 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu____13980 in
                                           solve env uu____13979))
                             | (x, imp)::formals2 ->
                                 let uu____14002 =
                                   let uu____14009 =
                                     let uu____14012 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____14012
                                       FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14009 wl1 in
                                 (match uu____14002 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu____14033 =
                                          let uu____14036 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some
                                            uu____14036 in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14033 u_x in
                                      let uu____14037 =
                                        let uu____14040 =
                                          let uu____14043 =
                                            let uu____14044 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y in
                                            (uu____14044, imp) in
                                          [uu____14043] in
                                        FStar_List.append bs_terms
                                          uu____14040 in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14037 formals2 wl2) in
                           let uu____14071 = occurs_check u_lhs arrow in
                           (match uu____14071 with
                            | (uu____14082, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14093 =
                                    mklstr
                                      (fun uu____14098 ->
                                         let uu____14099 =
                                           FStar_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14099) in
                                  giveup_or_defer env orig wl uu____14093
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
              (let uu____14128 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____14128
               then
                 let uu____14129 =
                   FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu____14130 =
                   FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14129 (rel_to_string (p_rel orig)) uu____14130
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu____14255 = rhs wl1 scope env1 subst in
                     (match uu____14255 with
                      | (rhs_prob, wl2) ->
                          ((let uu____14277 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu____14277
                            then
                              let uu____14278 = prob_to_string env1 rhs_prob in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14278
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1, imp)::xs1, (hd2, imp')::ys1) when
                     let uu____14351 = FStar_Syntax_Util.eq_aqual imp imp' in
                     uu____14351 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2295_14353 = hd1 in
                       let uu____14354 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2295_14353.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2295_14353.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14354
                       } in
                     let hd21 =
                       let uu___2298_14358 = hd2 in
                       let uu____14359 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2298_14358.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2298_14358.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14359
                       } in
                     let uu____14362 =
                       let uu____14367 =
                         FStar_All.pipe_left invert_rel (p_rel orig) in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____14367
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter" in
                     (match uu____14362 with
                      | (prob, wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                          let subst1 =
                            let uu____14388 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____14388 in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                          let uu____14392 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1 in
                          (match uu____14392 with
                           | (env3, FStar_Util.Inl (sub_probs, phi), wl3) ->
                               let phi1 =
                                 let uu____14460 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____14460 in
                               ((let uu____14478 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14478
                                 then
                                   let uu____14479 =
                                     FStar_Syntax_Print.term_to_string phi1 in
                                   let uu____14480 =
                                     FStar_Syntax_Print.bv_to_string hd12 in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____14479
                                     uu____14480
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____14509 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1) in
               let uu____14542 = aux wl [] env [] bs1 bs2 in
               match uu____14542 with
               | (env1, FStar_Util.Inr msg, wl1) -> giveup_lit env1 msg orig
               | (env1, FStar_Util.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu____14595 = attempt sub_probs wl2 in
                   solve env1 uu____14595)
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
            let uu___2336_14615 = wl in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2336_14615.wl_deferred_to_tac);
              ctr = (uu___2336_14615.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2336_14615.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2336_14615.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu____14623 = try_solve env wl' in
          match uu____14623 with
          | Success (uu____14624, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____14636 = compress_tprob wl.tcenv problem in
         solve_t' env uu____14636 wl)
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
            (let uu____14643 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Rel") in
             if uu____14643
             then FStar_Util.print_string "solve_t_flex_rigid_eq\n"
             else ());
            (let uu____14645 = should_defer_flex_to_user_tac env wl lhs in
             if uu____14645
             then defer_to_user_tac env orig (flex_reason lhs) wl
             else
               (let binders_as_bv_set bs =
                  let uu____14655 =
                    FStar_List.map FStar_Pervasives_Native.fst bs in
                  FStar_Util.as_set uu____14655 FStar_Syntax_Syntax.order_bv in
                let mk_solution env1 lhs1 bs rhs1 =
                  let uu____14689 = lhs1 in
                  match uu____14689 with
                  | Flex (uu____14692, ctx_u, uu____14694) ->
                      let sol =
                        match bs with
                        | [] -> rhs1
                        | uu____14702 ->
                            let uu____14703 = sn_binders env1 bs in
                            u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                              uu____14703 rhs1 in
                      [TERM (ctx_u, sol)] in
                let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                  (let uu____14751 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu____14751
                   then FStar_Util.print_string "try_quasi_pattern\n"
                   else ());
                  (let uu____14753 = quasi_pattern env1 lhs1 in
                   match uu____14753 with
                   | FStar_Pervasives_Native.None ->
                       ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                   | FStar_Pervasives_Native.Some (bs, uu____14783) ->
                       let uu____14788 = lhs1 in
                       (match uu____14788 with
                        | Flex (t_lhs, ctx_u, args) ->
                            let uu____14802 = occurs_check ctx_u rhs1 in
                            (match uu____14802 with
                             | (uvars, occurs_ok, msg) ->
                                 if Prims.op_Negation occurs_ok
                                 then
                                   let uu____14844 =
                                     let uu____14851 =
                                       let uu____14852 = FStar_Option.get msg in
                                       Prims.op_Hat
                                         "quasi-pattern, occurs-check failed: "
                                         uu____14852 in
                                     FStar_Util.Inl uu____14851 in
                                   (uu____14844, wl1)
                                 else
                                   (let fvs_lhs =
                                      binders_as_bv_set
                                        (FStar_List.append
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                           bs) in
                                    let fvs_rhs =
                                      FStar_Syntax_Free.names rhs1 in
                                    let uu____14874 =
                                      let uu____14875 =
                                        FStar_Util.set_is_subset_of fvs_rhs
                                          fvs_lhs in
                                      Prims.op_Negation uu____14875 in
                                    if uu____14874
                                    then
                                      ((FStar_Util.Inl
                                          "quasi-pattern, free names on the RHS are not included in the LHS"),
                                        wl1)
                                    else
                                      (let uu____14895 =
                                         let uu____14902 =
                                           mk_solution env1 lhs1 bs rhs1 in
                                         FStar_Util.Inr uu____14902 in
                                       let uu____14907 =
                                         restrict_all_uvars ctx_u uvars wl1 in
                                       (uu____14895, uu____14907)))))) in
                let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                  let uu____14950 = FStar_Syntax_Util.head_and_args rhs1 in
                  match uu____14950 with
                  | (rhs_hd, args) ->
                      let uu____14993 = FStar_Util.prefix args in
                      (match uu____14993 with
                       | (args_rhs, last_arg_rhs) ->
                           let rhs' =
                             FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                               rhs1.FStar_Syntax_Syntax.pos in
                           let uu____15063 = lhs1 in
                           (match uu____15063 with
                            | Flex (t_lhs, u_lhs, _lhs_args) ->
                                let uu____15067 =
                                  let uu____15078 =
                                    let uu____15085 =
                                      let uu____15088 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_left
                                        FStar_Pervasives_Native.fst
                                        uu____15088 in
                                    copy_uvar u_lhs [] uu____15085 wl1 in
                                  match uu____15078 with
                                  | (uu____15115, t_last_arg, wl2) ->
                                      let uu____15118 =
                                        let uu____15125 =
                                          let uu____15126 =
                                            let uu____15135 =
                                              FStar_Syntax_Syntax.null_binder
                                                t_last_arg in
                                            [uu____15135] in
                                          FStar_List.append bs_lhs
                                            uu____15126 in
                                        copy_uvar u_lhs uu____15125 t_res_lhs
                                          wl2 in
                                      (match uu____15118 with
                                       | (uu____15170, lhs', wl3) ->
                                           let uu____15173 =
                                             copy_uvar u_lhs bs_lhs
                                               t_last_arg wl3 in
                                           (match uu____15173 with
                                            | (uu____15190, lhs'_last_arg,
                                               wl4) ->
                                                (lhs', lhs'_last_arg, wl4))) in
                                (match uu____15067 with
                                 | (lhs', lhs'_last_arg, wl2) ->
                                     let sol =
                                       let uu____15211 =
                                         let uu____15212 =
                                           let uu____15217 =
                                             let uu____15218 =
                                               let uu____15221 =
                                                 let uu____15222 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lhs'_last_arg in
                                                 [uu____15222] in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 lhs' uu____15221
                                                 t_lhs.FStar_Syntax_Syntax.pos in
                                             FStar_Syntax_Util.abs bs_lhs
                                               uu____15218
                                               (FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Util.residual_tot
                                                     t_res_lhs)) in
                                           (u_lhs, uu____15217) in
                                         TERM uu____15212 in
                                       [uu____15211] in
                                     let uu____15247 =
                                       let uu____15254 =
                                         mk_t_problem wl2 [] orig1 lhs'
                                           FStar_TypeChecker_Common.EQ rhs'
                                           FStar_Pervasives_Native.None
                                           "first-order lhs" in
                                       match uu____15254 with
                                       | (p1, wl3) ->
                                           let uu____15273 =
                                             mk_t_problem wl3 [] orig1
                                               lhs'_last_arg
                                               FStar_TypeChecker_Common.EQ
                                               (FStar_Pervasives_Native.fst
                                                  last_arg_rhs)
                                               FStar_Pervasives_Native.None
                                               "first-order rhs" in
                                           (match uu____15273 with
                                            | (p2, wl4) -> ([p1; p2], wl4)) in
                                     (match uu____15247 with
                                      | (sub_probs, wl3) ->
                                          let uu____15304 =
                                            let uu____15305 =
                                              solve_prob orig1
                                                FStar_Pervasives_Native.None
                                                sol wl3 in
                                            attempt sub_probs uu____15305 in
                                          solve env1 uu____15304)))) in
                let first_order orig1 env1 wl1 lhs1 rhs1 =
                  (let uu____15333 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu____15333
                   then FStar_Util.print_string "first_order\n"
                   else ());
                  (let is_app rhs2 =
                     let uu____15341 = FStar_Syntax_Util.head_and_args rhs2 in
                     match uu____15341 with
                     | (uu____15358, args) ->
                         (match args with | [] -> false | uu____15392 -> true) in
                   let is_arrow rhs2 =
                     let uu____15409 =
                       let uu____15410 = FStar_Syntax_Subst.compress rhs2 in
                       uu____15410.FStar_Syntax_Syntax.n in
                     match uu____15409 with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15413 -> true
                     | uu____15428 -> false in
                   let uu____15429 = quasi_pattern env1 lhs1 in
                   match uu____15429 with
                   | FStar_Pervasives_Native.None ->
                       let msg =
                         mklstr
                           (fun uu____15447 ->
                              let uu____15448 = prob_to_string env1 orig1 in
                              FStar_Util.format1
                                "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                                uu____15448) in
                       giveup_or_defer env1 orig1 wl1 msg
                   | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                       let uu____15455 = is_app rhs1 in
                       if uu____15455
                       then
                         imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                           rhs1
                       else
                         (let uu____15457 = is_arrow rhs1 in
                          if uu____15457
                          then
                            imitate_arrow orig1 env1 wl1 lhs1 bs_lhs
                              t_res_lhs FStar_TypeChecker_Common.EQ rhs1
                          else
                            (let msg =
                               mklstr
                                 (fun uu____15466 ->
                                    let uu____15467 =
                                      prob_to_string env1 orig1 in
                                    FStar_Util.format1
                                      "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                      uu____15467) in
                             giveup_or_defer env1 orig1 wl1 msg))) in
                match p_rel orig with
                | FStar_TypeChecker_Common.SUB ->
                    if wl.defer_ok
                    then
                      let uu____15468 =
                        FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl uu____15468
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.SUBINV ->
                    if wl.defer_ok
                    then
                      let uu____15470 =
                        FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl uu____15470
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.EQ ->
                    let uu____15472 = lhs in
                    (match uu____15472 with
                     | Flex (_t1, ctx_uv, args_lhs) ->
                         let uu____15476 =
                           pat_vars env
                             ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                             args_lhs in
                         (match uu____15476 with
                          | FStar_Pervasives_Native.Some lhs_binders ->
                              ((let uu____15483 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel") in
                                if uu____15483
                                then
                                  FStar_Util.print_string "it's a pattern\n"
                                else ());
                               (let rhs1 = sn env rhs in
                                let names_to_string1 fvs =
                                  let uu____15496 =
                                    let uu____15499 =
                                      FStar_Util.set_elements fvs in
                                    FStar_List.map
                                      FStar_Syntax_Print.bv_to_string
                                      uu____15499 in
                                  FStar_All.pipe_right uu____15496
                                    (FStar_String.concat ", ") in
                                let fvs1 =
                                  binders_as_bv_set
                                    (FStar_List.append
                                       ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                       lhs_binders) in
                                let fvs2 = FStar_Syntax_Free.names rhs1 in
                                let uu____15516 = occurs_check ctx_uv rhs1 in
                                match uu____15516 with
                                | (uvars, occurs_ok, msg) ->
                                    if Prims.op_Negation occurs_ok
                                    then
                                      let uu____15538 =
                                        let uu____15539 =
                                          let uu____15540 =
                                            FStar_Option.get msg in
                                          Prims.op_Hat
                                            "occurs-check failed: "
                                            uu____15540 in
                                        FStar_All.pipe_left FStar_Thunk.mkv
                                          uu____15539 in
                                      giveup_or_defer env orig wl uu____15538
                                    else
                                      (let uu____15542 =
                                         FStar_Util.set_is_subset_of fvs2
                                           fvs1 in
                                       if uu____15542
                                       then
                                         let sol =
                                           mk_solution env lhs lhs_binders
                                             rhs1 in
                                         let wl1 =
                                           restrict_all_uvars ctx_uv uvars wl in
                                         let uu____15547 =
                                           solve_prob orig
                                             FStar_Pervasives_Native.None sol
                                             wl1 in
                                         solve env uu____15547
                                       else
                                         if wl.defer_ok
                                         then
                                           (let msg1 =
                                              mklstr
                                                (fun uu____15560 ->
                                                   let uu____15561 =
                                                     names_to_string1 fvs2 in
                                                   let uu____15562 =
                                                     names_to_string1 fvs1 in
                                                   let uu____15563 =
                                                     FStar_Syntax_Print.binders_to_string
                                                       ", "
                                                       (FStar_List.append
                                                          ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                          lhs_binders) in
                                                   FStar_Util.format3
                                                     "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                     uu____15561 uu____15562
                                                     uu____15563) in
                                            giveup_or_defer env orig wl msg1)
                                         else
                                           first_order orig env wl lhs rhs1)))
                          | uu____15571 ->
                              if wl.defer_ok
                              then
                                let uu____15574 =
                                  FStar_Thunk.mkv "Not a pattern" in
                                giveup_or_defer env orig wl uu____15574
                              else
                                (let uu____15576 =
                                   try_quasi_pattern orig env wl lhs rhs in
                                 match uu____15576 with
                                 | (FStar_Util.Inr sol, wl1) ->
                                     let uu____15599 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None sol wl1 in
                                     solve env uu____15599
                                 | (FStar_Util.Inl msg, uu____15601) ->
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
                  let uu____15615 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15615
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok
                then
                  let uu____15617 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15617
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu____15619 =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu____15619
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
                    (let uu____15621 =
                       FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer env orig wl uu____15621)
                  else
                    (let uu____15623 =
                       let uu____15640 = quasi_pattern env lhs in
                       let uu____15647 = quasi_pattern env rhs in
                       (uu____15640, uu____15647) in
                     match uu____15623 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs, t_res_lhs),
                        FStar_Pervasives_Native.Some
                        (binders_rhs, t_res_rhs)) ->
                         let uu____15690 = lhs in
                         (match uu____15690 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____15691;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____15693;_},
                               u_lhs, uu____15695)
                              ->
                              let uu____15698 = rhs in
                              (match uu____15698 with
                               | Flex (uu____15699, u_rhs, uu____15701) ->
                                   let uu____15702 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs) in
                                   if uu____15702
                                   then
                                     let uu____15707 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl in
                                     solve env uu____15707
                                   else
                                     (let uu____15709 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                      match uu____15709 with
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
                                          let uu____15741 =
                                            let uu____15748 =
                                              let uu____15751 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs in
                                              FStar_Syntax_Util.arrow zs
                                                uu____15751 in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____15748
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
                                          (match uu____15741 with
                                           | (uu____15755, w, wl1) ->
                                               let w_app =
                                                 let uu____15759 =
                                                   FStar_List.map
                                                     (fun uu____15770 ->
                                                        match uu____15770
                                                        with
                                                        | (z, uu____15778) ->
                                                            let uu____15783 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____15783) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____15759
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____15785 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____15785
                                                 then
                                                   let uu____15786 =
                                                     let uu____15789 =
                                                       flex_t_to_string lhs in
                                                     let uu____15790 =
                                                       let uu____15793 =
                                                         flex_t_to_string rhs in
                                                       let uu____15794 =
                                                         let uu____15797 =
                                                           term_to_string w in
                                                         let uu____15798 =
                                                           let uu____15801 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____15808 =
                                                             let uu____15811
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____15818
                                                               =
                                                               let uu____15821
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____15821] in
                                                             uu____15811 ::
                                                               uu____15818 in
                                                           uu____15801 ::
                                                             uu____15808 in
                                                         uu____15797 ::
                                                           uu____15798 in
                                                       uu____15793 ::
                                                         uu____15794 in
                                                     uu____15789 ::
                                                       uu____15790 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____15786
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____15827 =
                                                       let uu____15832 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____15832) in
                                                     TERM uu____15827 in
                                                   let uu____15833 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____15833
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____15838 =
                                                          let uu____15843 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____15843) in
                                                        TERM uu____15838 in
                                                      [s1; s2]) in
                                                 let uu____15844 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____15844))))))
                     | uu____15845 ->
                         let uu____15862 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____15862)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____15911 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____15911
            then
              let uu____15912 = FStar_Syntax_Print.term_to_string t1 in
              let uu____15913 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____15914 = FStar_Syntax_Print.term_to_string t2 in
              let uu____15915 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15912 uu____15913 uu____15914 uu____15915
            else ());
           (let uu____15918 = FStar_Syntax_Util.head_and_args t1 in
            match uu____15918 with
            | (head1, args1) ->
                let uu____15961 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____15961 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16026 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____16026 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____16030 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____16030) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16048 =
                         mklstr
                           (fun uu____16059 ->
                              let uu____16060 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____16061 = args_to_string args1 in
                              let uu____16064 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____16065 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____16060 uu____16061 uu____16064
                                uu____16065) in
                       giveup env1 uu____16048 orig
                     else
                       (let uu____16069 =
                          (nargs = Prims.int_zero) ||
                            (let uu____16071 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____16071 = FStar_Syntax_Util.Equal) in
                        if uu____16069
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2617_16073 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2617_16073.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2617_16073.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2617_16073.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2617_16073.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2617_16073.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2617_16073.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2617_16073.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2617_16073.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____16080 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____16080
                                    else solve env1 wl2))
                        else
                          (let uu____16083 = base_and_refinement env1 t1 in
                           match uu____16083 with
                           | (base1, refinement1) ->
                               let uu____16108 = base_and_refinement env1 t2 in
                               (match uu____16108 with
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
                                           let uu____16271 =
                                             FStar_List.fold_right
                                               (fun uu____16311 ->
                                                  fun uu____16312 ->
                                                    match (uu____16311,
                                                            uu____16312)
                                                    with
                                                    | (((a1, uu____16364),
                                                        (a2, uu____16366)),
                                                       (probs, wl3)) ->
                                                        let uu____16415 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____16415
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____16271 with
                                           | (subprobs, wl3) ->
                                               ((let uu____16457 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16457
                                                 then
                                                   let uu____16458 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____16458
                                                 else ());
                                                (let uu____16461 =
                                                   FStar_Options.defensive () in
                                                 if uu____16461
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
                                                    (let uu____16481 =
                                                       mk_sub_probs wl3 in
                                                     match uu____16481 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____16497 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____16497 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____16505 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____16505)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____16529 =
                                                    mk_sub_probs wl3 in
                                                  match uu____16529 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____16545 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____16545 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____16553 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____16553) in
                                         let unfold_and_retry d env2 wl2
                                           uu____16580 =
                                           match uu____16580 with
                                           | (prob, reason) ->
                                               ((let uu____16594 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16594
                                                 then
                                                   let uu____16595 =
                                                     prob_to_string env2 orig in
                                                   let uu____16596 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____16595 uu____16596
                                                 else ());
                                                (let uu____16598 =
                                                   let uu____16607 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____16610 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____16607, uu____16610) in
                                                 match uu____16598 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____16623 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____16623 with
                                                      | (head1', uu____16641)
                                                          ->
                                                          let uu____16666 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____16666
                                                           with
                                                           | (head2',
                                                              uu____16684) ->
                                                               let uu____16709
                                                                 =
                                                                 let uu____16714
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____16715
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____16714,
                                                                   uu____16715) in
                                                               (match uu____16709
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu____16717
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____16717
                                                                    then
                                                                    let uu____16718
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____16719
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____16720
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____16721
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____16718
                                                                    uu____16719
                                                                    uu____16720
                                                                    uu____16721
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____16723
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2705_16731
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2705_16731.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2705_16731.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2705_16731.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2705_16731.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2705_16731.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2705_16731.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2705_16731.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2705_16731.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
                                                                    let uu____16733
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____16733
                                                                    then
                                                                    let uu____16734
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____16734
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____16736 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____16748 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____16748 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____16755 =
                                             let uu____16756 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____16756.FStar_Syntax_Syntax.n in
                                           match uu____16755 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____16760 -> false in
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
                                          | uu____16762 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____16765 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2725_16801 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2725_16801.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2725_16801.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2725_16801.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2725_16801.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2725_16801.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2725_16801.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2725_16801.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2725_16801.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16876 = destruct_flex_t scrutinee wl1 in
             match uu____16876 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____16887 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____16887 with
                  | (xs, pat_term, uu____16902, uu____16903) ->
                      let uu____16908 =
                        FStar_List.fold_left
                          (fun uu____16931 ->
                             fun x ->
                               match uu____16931 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____16952 = copy_uvar uv [] t_x wl3 in
                                   (match uu____16952 with
                                    | (uu____16971, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____16908 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____16992 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____16992 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2766_17008 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2766_17008.wl_deferred_to_tac);
                                    ctr = (uu___2766_17008.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2766_17008.umax_heuristic_ok);
                                    tcenv = (uu___2766_17008.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2766_17008.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____17016 = solve env1 wl' in
                                (match uu____17016 with
                                 | Success (uu____17019, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2775_17023 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2775_17023.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2775_17023.wl_deferred_to_tac);
                                         ctr = (uu___2775_17023.ctr);
                                         defer_ok =
                                           (uu___2775_17023.defer_ok);
                                         smt_ok = (uu___2775_17023.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2775_17023.umax_heuristic_ok);
                                         tcenv = (uu___2775_17023.tcenv);
                                         wl_implicits =
                                           (uu___2775_17023.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2775_17023.repr_subcomp_allowed)
                                       } in
                                     let uu____17024 = solve env1 wl'1 in
                                     (match uu____17024 with
                                      | Success
                                          (uu____17027, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____17031 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____17031))
                                      | Failed uu____17036 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17042 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____17063 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____17063
                 then
                   let uu____17064 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____17065 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17064 uu____17065
                 else ());
                (let uu____17067 =
                   let uu____17088 =
                     let uu____17097 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____17097) in
                   let uu____17104 =
                     let uu____17113 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____17113) in
                   (uu____17088, uu____17104) in
                 match uu____17067 with
                 | ((uu____17142,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____17145;
                       FStar_Syntax_Syntax.vars = uu____17146;_}),
                    (s, t)) ->
                     let uu____17217 =
                       let uu____17218 = is_flex scrutinee in
                       Prims.op_Negation uu____17218 in
                     if uu____17217
                     then
                       ((let uu____17226 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____17226
                         then
                           let uu____17227 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17227
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17239 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17239
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17245 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17245
                           then
                             let uu____17246 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____17247 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17246 uu____17247
                           else ());
                          (let pat_discriminates uu___26_17268 =
                             match uu___26_17268 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17283;
                                  FStar_Syntax_Syntax.p = uu____17284;_},
                                FStar_Pervasives_Native.None, uu____17285) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17298;
                                  FStar_Syntax_Syntax.p = uu____17299;_},
                                FStar_Pervasives_Native.None, uu____17300) ->
                                 true
                             | uu____17325 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____17425 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____17425 with
                                       | (uu____17426, uu____17427, t') ->
                                           let uu____17445 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____17445 with
                                            | (FullMatch, uu____17456) ->
                                                true
                                            | (HeadMatch uu____17469,
                                               uu____17470) -> true
                                            | uu____17483 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____17516 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____17516
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17521 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____17521 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____17609, uu____17610)
                                       -> branches1
                                   | uu____17755 -> branches in
                                 let uu____17810 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____17819 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____17819 with
                                        | (p, uu____17823, uu____17824) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____17851 ->
                                      FStar_Util.Inr uu____17851) uu____17810))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17881 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____17881 with
                                | (p, uu____17889, e) ->
                                    ((let uu____17908 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____17908
                                      then
                                        let uu____17909 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____17910 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17909 uu____17910
                                      else ());
                                     (let uu____17912 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____17925 ->
                                           FStar_Util.Inr uu____17925)
                                        uu____17912)))))
                 | ((s, t),
                    (uu____17928,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____17931;
                       FStar_Syntax_Syntax.vars = uu____17932;_}))
                     ->
                     let uu____18001 =
                       let uu____18002 = is_flex scrutinee in
                       Prims.op_Negation uu____18002 in
                     if uu____18001
                     then
                       ((let uu____18010 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____18010
                         then
                           let uu____18011 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18011
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18023 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18023
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18029 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18029
                           then
                             let uu____18030 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____18031 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18030 uu____18031
                           else ());
                          (let pat_discriminates uu___26_18052 =
                             match uu___26_18052 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18067;
                                  FStar_Syntax_Syntax.p = uu____18068;_},
                                FStar_Pervasives_Native.None, uu____18069) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18082;
                                  FStar_Syntax_Syntax.p = uu____18083;_},
                                FStar_Pervasives_Native.None, uu____18084) ->
                                 true
                             | uu____18109 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____18209 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____18209 with
                                       | (uu____18210, uu____18211, t') ->
                                           let uu____18229 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____18229 with
                                            | (FullMatch, uu____18240) ->
                                                true
                                            | (HeadMatch uu____18253,
                                               uu____18254) -> true
                                            | uu____18267 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____18300 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____18300
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18305 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____18305 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____18393, uu____18394)
                                       -> branches1
                                   | uu____18539 -> branches in
                                 let uu____18594 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____18603 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____18603 with
                                        | (p, uu____18607, uu____18608) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____18635 ->
                                      FStar_Util.Inr uu____18635) uu____18594))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18665 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____18665 with
                                | (p, uu____18673, e) ->
                                    ((let uu____18692 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____18692
                                      then
                                        let uu____18693 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____18694 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18693 uu____18694
                                      else ());
                                     (let uu____18696 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____18709 ->
                                           FStar_Util.Inr uu____18709)
                                        uu____18696)))))
                 | uu____18710 ->
                     ((let uu____18732 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____18732
                       then
                         let uu____18733 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____18734 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____18733 uu____18734
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____18776 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____18776
            then
              let uu____18777 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____18778 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____18779 = FStar_Syntax_Print.term_to_string t1 in
              let uu____18780 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____18777 uu____18778 uu____18779 uu____18780
            else ());
           (let uu____18782 = head_matches_delta env1 wl1 t1 t2 in
            match uu____18782 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____18813, uu____18814) ->
                     let rec may_relate head =
                       let uu____18841 =
                         let uu____18842 = FStar_Syntax_Subst.compress head in
                         uu____18842.FStar_Syntax_Syntax.n in
                       match uu____18841 with
                       | FStar_Syntax_Syntax.Tm_name uu____18845 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18846 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____18870 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____18870 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____18871 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____18872
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____18873 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____18875, uu____18876) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____18918) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____18924) ->
                           may_relate t
                       | uu____18929 -> false in
                     let uu____18930 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____18930 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____18940 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____18940
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____18946 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____18946
                          then
                            let uu____18947 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____18947 with
                             | (guard, wl2) ->
                                 let uu____18954 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____18954)
                          else
                            (let uu____18956 =
                               mklstr
                                 (fun uu____18967 ->
                                    let uu____18968 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____18969 =
                                      let uu____18970 =
                                        let uu____18973 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____18973
                                          (fun x ->
                                             let uu____18979 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____18979) in
                                      FStar_Util.dflt "" uu____18970 in
                                    let uu____18980 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____18981 =
                                      let uu____18982 =
                                        let uu____18985 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____18985
                                          (fun x ->
                                             let uu____18991 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____18991) in
                                      FStar_Util.dflt "" uu____18982 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____18968 uu____18969 uu____18980
                                      uu____18981) in
                             giveup env1 uu____18956 orig))
                 | (HeadMatch (true), uu____18992) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____19005 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____19005 with
                        | (guard, wl2) ->
                            let uu____19012 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____19012)
                     else
                       (let uu____19014 =
                          mklstr
                            (fun uu____19021 ->
                               let uu____19022 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____19023 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____19022 uu____19023) in
                        giveup env1 uu____19014 orig)
                 | (uu____19024, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2957_19038 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2957_19038.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2957_19038.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2957_19038.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2957_19038.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2957_19038.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2957_19038.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2957_19038.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2957_19038.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____19062 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____19062
          then
            let uu____19063 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____19063
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____19068 =
                let uu____19071 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19071 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____19068 t1);
             (let uu____19089 =
                let uu____19092 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19092 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____19089 t2);
             (let uu____19110 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____19110
              then
                let uu____19111 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____19112 =
                  let uu____19113 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____19114 =
                    let uu____19115 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____19115 in
                  Prims.op_Hat uu____19113 uu____19114 in
                let uu____19116 =
                  let uu____19117 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____19118 =
                    let uu____19119 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____19119 in
                  Prims.op_Hat uu____19117 uu____19118 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____19111 uu____19112 uu____19116
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____19122, uu____19123) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____19138, FStar_Syntax_Syntax.Tm_delayed uu____19139) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____19154, uu____19155) ->
                  let uu____19182 =
                    let uu___2988_19183 = problem in
                    let uu____19184 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2988_19183.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19184;
                      FStar_TypeChecker_Common.relation =
                        (uu___2988_19183.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2988_19183.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2988_19183.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2988_19183.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2988_19183.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2988_19183.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2988_19183.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2988_19183.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19182 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____19185, uu____19186) ->
                  let uu____19193 =
                    let uu___2994_19194 = problem in
                    let uu____19195 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2994_19194.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19195;
                      FStar_TypeChecker_Common.relation =
                        (uu___2994_19194.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2994_19194.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2994_19194.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2994_19194.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2994_19194.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2994_19194.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2994_19194.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2994_19194.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19193 wl
              | (uu____19196, FStar_Syntax_Syntax.Tm_ascribed uu____19197) ->
                  let uu____19224 =
                    let uu___3000_19225 = problem in
                    let uu____19226 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3000_19225.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3000_19225.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3000_19225.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19226;
                      FStar_TypeChecker_Common.element =
                        (uu___3000_19225.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3000_19225.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3000_19225.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3000_19225.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3000_19225.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3000_19225.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19224 wl
              | (uu____19227, FStar_Syntax_Syntax.Tm_meta uu____19228) ->
                  let uu____19235 =
                    let uu___3006_19236 = problem in
                    let uu____19237 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3006_19236.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3006_19236.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3006_19236.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19237;
                      FStar_TypeChecker_Common.element =
                        (uu___3006_19236.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3006_19236.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3006_19236.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3006_19236.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3006_19236.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3006_19236.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19235 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____19239),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____19241)) ->
                  let uu____19250 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____19250
              | (FStar_Syntax_Syntax.Tm_bvar uu____19251, uu____19252) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____19253, FStar_Syntax_Syntax.Tm_bvar uu____19254) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_19323 =
                    match uu___27_19323 with
                    | [] -> c
                    | bs ->
                        let uu____19351 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____19351 in
                  let uu____19362 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____19362 with
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
                                    let uu____19511 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____19511
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_19596 =
                    match uu___28_19596 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____19638 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____19638 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____19783 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____19784 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____19783
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____19784 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____19785, uu____19786) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19815 -> true
                    | uu____19834 -> false in
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
                      (let uu____19887 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3108_19895 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3108_19895.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3108_19895.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3108_19895.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3108_19895.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3108_19895.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3108_19895.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3108_19895.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3108_19895.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3108_19895.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3108_19895.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3108_19895.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3108_19895.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3108_19895.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3108_19895.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3108_19895.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3108_19895.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3108_19895.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3108_19895.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3108_19895.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3108_19895.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3108_19895.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3108_19895.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3108_19895.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3108_19895.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3108_19895.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3108_19895.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3108_19895.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3108_19895.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3108_19895.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3108_19895.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3108_19895.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3108_19895.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3108_19895.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3108_19895.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3108_19895.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3108_19895.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3108_19895.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3108_19895.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3108_19895.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3108_19895.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3108_19895.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3108_19895.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3108_19895.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3108_19895.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____19887 with
                       | (uu____19898, ty, uu____19900) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____19909 =
                                 let uu____19910 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____19910.FStar_Syntax_Syntax.n in
                               match uu____19909 with
                               | FStar_Syntax_Syntax.Tm_refine uu____19913 ->
                                   let uu____19920 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____19920
                               | uu____19921 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____19924 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____19924
                             then
                               let uu____19925 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____19926 =
                                 let uu____19927 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____19927 in
                               let uu____19928 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____19925 uu____19926 uu____19928
                             else ());
                            r1)) in
                  let uu____19930 =
                    let uu____19947 = maybe_eta t1 in
                    let uu____19954 = maybe_eta t2 in
                    (uu____19947, uu____19954) in
                  (match uu____19930 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3129_19996 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3129_19996.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3129_19996.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3129_19996.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3129_19996.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3129_19996.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3129_19996.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3129_19996.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3129_19996.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20017 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20017
                       then
                         let uu____20018 = destruct_flex_t not_abs wl in
                         (match uu____20018 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3146_20033 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3146_20033.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3146_20033.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3146_20033.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3146_20033.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3146_20033.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3146_20033.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3146_20033.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3146_20033.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20035 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20035 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20056 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20056
                       then
                         let uu____20057 = destruct_flex_t not_abs wl in
                         (match uu____20057 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3146_20072 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3146_20072.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3146_20072.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3146_20072.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3146_20072.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3146_20072.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3146_20072.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3146_20072.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3146_20072.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20074 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20074 orig))
                   | uu____20075 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____20092, FStar_Syntax_Syntax.Tm_abs uu____20093) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20122 -> true
                    | uu____20141 -> false in
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
                      (let uu____20194 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3108_20202 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3108_20202.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3108_20202.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3108_20202.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3108_20202.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3108_20202.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3108_20202.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3108_20202.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3108_20202.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3108_20202.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3108_20202.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3108_20202.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3108_20202.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3108_20202.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3108_20202.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3108_20202.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3108_20202.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3108_20202.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3108_20202.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3108_20202.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3108_20202.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3108_20202.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3108_20202.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3108_20202.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3108_20202.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3108_20202.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3108_20202.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3108_20202.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3108_20202.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3108_20202.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3108_20202.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3108_20202.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3108_20202.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3108_20202.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3108_20202.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3108_20202.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3108_20202.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3108_20202.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3108_20202.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3108_20202.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3108_20202.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3108_20202.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3108_20202.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3108_20202.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3108_20202.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____20194 with
                       | (uu____20205, ty, uu____20207) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____20216 =
                                 let uu____20217 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____20217.FStar_Syntax_Syntax.n in
                               match uu____20216 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20220 ->
                                   let uu____20227 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____20227
                               | uu____20228 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____20231 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____20231
                             then
                               let uu____20232 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____20233 =
                                 let uu____20234 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20234 in
                               let uu____20235 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20232 uu____20233 uu____20235
                             else ());
                            r1)) in
                  let uu____20237 =
                    let uu____20254 = maybe_eta t1 in
                    let uu____20261 = maybe_eta t2 in
                    (uu____20254, uu____20261) in
                  (match uu____20237 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3129_20303 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3129_20303.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3129_20303.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3129_20303.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3129_20303.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3129_20303.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3129_20303.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3129_20303.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3129_20303.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20324 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20324
                       then
                         let uu____20325 = destruct_flex_t not_abs wl in
                         (match uu____20325 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3146_20340 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3146_20340.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3146_20340.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3146_20340.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3146_20340.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3146_20340.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3146_20340.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3146_20340.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3146_20340.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20342 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20342 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20363 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20363
                       then
                         let uu____20364 = destruct_flex_t not_abs wl in
                         (match uu____20364 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3146_20379 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3146_20379.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3146_20379.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3146_20379.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3146_20379.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3146_20379.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3146_20379.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3146_20379.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3146_20379.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20381 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20381 orig))
                   | uu____20382 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____20411 =
                    let uu____20416 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____20416 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3169_20444 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3169_20444.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3169_20444.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3171_20446 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3171_20446.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3171_20446.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____20447, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3169_20461 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3169_20461.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3169_20461.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3171_20463 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3171_20463.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3171_20463.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____20464 -> (x1, x2) in
                  (match uu____20411 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____20483 = as_refinement false env t11 in
                       (match uu____20483 with
                        | (x12, phi11) ->
                            let uu____20490 = as_refinement false env t21 in
                            (match uu____20490 with
                             | (x22, phi21) ->
                                 ((let uu____20498 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____20498
                                   then
                                     ((let uu____20500 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____20501 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____20502 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____20500
                                         uu____20501 uu____20502);
                                      (let uu____20503 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____20504 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____20505 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____20503
                                         uu____20504 uu____20505))
                                   else ());
                                  (let uu____20507 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____20507 with
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
                                         let uu____20575 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____20575
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____20587 =
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
                                         (let uu____20598 =
                                            let uu____20601 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20601 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____20598
                                            (p_guard base_prob));
                                         (let uu____20619 =
                                            let uu____20622 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20622 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____20619
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____20640 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____20640) in
                                       let has_uvars =
                                         (let uu____20644 =
                                            let uu____20645 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____20645 in
                                          Prims.op_Negation uu____20644) ||
                                           (let uu____20649 =
                                              let uu____20650 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____20650 in
                                            Prims.op_Negation uu____20649) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____20653 =
                                           let uu____20658 =
                                             let uu____20667 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____20667] in
                                           mk_t_problem wl1 uu____20658 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____20653 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____20689 =
                                                solve env1
                                                  (let uu___3214_20691 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3214_20691.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3214_20691.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3214_20691.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3214_20691.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3214_20691.tcenv);
                                                     wl_implicits =
                                                       (uu___3214_20691.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3214_20691.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____20689 with
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
                                                   (uu____20702,
                                                    defer_to_tac,
                                                    uu____20704)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____20709 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____20709 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3230_20718 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3230_20718.attempting);
                                                         wl_deferred =
                                                           (uu___3230_20718.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3230_20718.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3230_20718.defer_ok);
                                                         smt_ok =
                                                           (uu___3230_20718.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3230_20718.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3230_20718.tcenv);
                                                         wl_implicits =
                                                           (uu___3230_20718.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3230_20718.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____20720 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____20720))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20722,
                 FStar_Syntax_Syntax.Tm_uvar uu____20723) ->
                  let uu____20748 = ensure_no_uvar_subst t1 wl in
                  (match uu____20748 with
                   | (t11, wl1) ->
                       let uu____20755 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20755 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20764;
                    FStar_Syntax_Syntax.pos = uu____20765;
                    FStar_Syntax_Syntax.vars = uu____20766;_},
                  uu____20767),
                 FStar_Syntax_Syntax.Tm_uvar uu____20768) ->
                  let uu____20817 = ensure_no_uvar_subst t1 wl in
                  (match uu____20817 with
                   | (t11, wl1) ->
                       let uu____20824 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20824 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20833,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20834;
                    FStar_Syntax_Syntax.pos = uu____20835;
                    FStar_Syntax_Syntax.vars = uu____20836;_},
                  uu____20837)) ->
                  let uu____20886 = ensure_no_uvar_subst t1 wl in
                  (match uu____20886 with
                   | (t11, wl1) ->
                       let uu____20893 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20893 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20902;
                    FStar_Syntax_Syntax.pos = uu____20903;
                    FStar_Syntax_Syntax.vars = uu____20904;_},
                  uu____20905),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20906;
                    FStar_Syntax_Syntax.pos = uu____20907;
                    FStar_Syntax_Syntax.vars = uu____20908;_},
                  uu____20909)) ->
                  let uu____20982 = ensure_no_uvar_subst t1 wl in
                  (match uu____20982 with
                   | (t11, wl1) ->
                       let uu____20989 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20989 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20998, uu____20999) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21012 = destruct_flex_t t1 wl in
                  (match uu____21012 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21019;
                    FStar_Syntax_Syntax.pos = uu____21020;
                    FStar_Syntax_Syntax.vars = uu____21021;_},
                  uu____21022),
                 uu____21023) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21060 = destruct_flex_t t1 wl in
                  (match uu____21060 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____21067, FStar_Syntax_Syntax.Tm_uvar uu____21068) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____21081, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21082;
                    FStar_Syntax_Syntax.pos = uu____21083;
                    FStar_Syntax_Syntax.vars = uu____21084;_},
                  uu____21085)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____21122,
                 FStar_Syntax_Syntax.Tm_arrow uu____21123) ->
                  solve_t' env
                    (let uu___3333_21151 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3333_21151.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3333_21151.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3333_21151.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3333_21151.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3333_21151.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3333_21151.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3333_21151.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3333_21151.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3333_21151.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21152;
                    FStar_Syntax_Syntax.pos = uu____21153;
                    FStar_Syntax_Syntax.vars = uu____21154;_},
                  uu____21155),
                 FStar_Syntax_Syntax.Tm_arrow uu____21156) ->
                  solve_t' env
                    (let uu___3333_21208 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3333_21208.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3333_21208.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3333_21208.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3333_21208.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3333_21208.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3333_21208.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3333_21208.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3333_21208.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3333_21208.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21209, FStar_Syntax_Syntax.Tm_uvar uu____21210) ->
                  let uu____21223 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21223
              | (uu____21224, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21225;
                    FStar_Syntax_Syntax.pos = uu____21226;
                    FStar_Syntax_Syntax.vars = uu____21227;_},
                  uu____21228)) ->
                  let uu____21265 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21265
              | (FStar_Syntax_Syntax.Tm_uvar uu____21266, uu____21267) ->
                  let uu____21280 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21280
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21281;
                    FStar_Syntax_Syntax.pos = uu____21282;
                    FStar_Syntax_Syntax.vars = uu____21283;_},
                  uu____21284),
                 uu____21285) ->
                  let uu____21322 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21322
              | (FStar_Syntax_Syntax.Tm_refine uu____21323, uu____21324) ->
                  let t21 =
                    let uu____21332 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____21332 in
                  solve_t env
                    (let uu___3368_21358 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3368_21358.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3368_21358.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3368_21358.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3368_21358.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3368_21358.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3368_21358.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3368_21358.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3368_21358.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3368_21358.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21359, FStar_Syntax_Syntax.Tm_refine uu____21360) ->
                  let t11 =
                    let uu____21368 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____21368 in
                  solve_t env
                    (let uu___3375_21394 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3375_21394.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3375_21394.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3375_21394.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3375_21394.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3375_21394.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3375_21394.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3375_21394.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3375_21394.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3375_21394.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____21476 =
                    let uu____21477 = guard_of_prob env wl problem t1 t2 in
                    match uu____21477 with
                    | (guard, wl1) ->
                        let uu____21484 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____21484 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____21703 = br1 in
                        (match uu____21703 with
                         | (p1, w1, uu____21732) ->
                             let uu____21749 = br2 in
                             (match uu____21749 with
                              | (p2, w2, uu____21772) ->
                                  let uu____21777 =
                                    let uu____21778 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____21778 in
                                  if uu____21777
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____21802 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____21802 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____21839 = br2 in
                                         (match uu____21839 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____21872 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____21872 in
                                              let uu____21877 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____21908,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____21929) ->
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
                                                    let uu____21988 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____21988 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____21877
                                                (fun uu____22059 ->
                                                   match uu____22059 with
                                                   | (wprobs, wl2) ->
                                                       let uu____22096 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____22096
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____22116
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____22116
                                                              then
                                                                let uu____22117
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____22118
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____22117
                                                                  uu____22118
                                                              else ());
                                                             (let uu____22120
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____22120
                                                                (fun
                                                                   uu____22156
                                                                   ->
                                                                   match uu____22156
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
                    | uu____22285 -> FStar_Pervasives_Native.None in
                  let uu____22326 = solve_branches wl brs1 brs2 in
                  (match uu____22326 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____22350 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____22350 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____22375 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____22375 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____22408 =
                                FStar_List.map
                                  (fun uu____22420 ->
                                     match uu____22420 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____22408 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____22429 =
                              let uu____22430 =
                                let uu____22431 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____22431
                                  (let uu___3474_22439 = wl3 in
                                   {
                                     attempting =
                                       (uu___3474_22439.attempting);
                                     wl_deferred =
                                       (uu___3474_22439.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3474_22439.wl_deferred_to_tac);
                                     ctr = (uu___3474_22439.ctr);
                                     defer_ok = (uu___3474_22439.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3474_22439.umax_heuristic_ok);
                                     tcenv = (uu___3474_22439.tcenv);
                                     wl_implicits =
                                       (uu___3474_22439.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3474_22439.repr_subcomp_allowed)
                                   }) in
                              solve env uu____22430 in
                            (match uu____22429 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____22444 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____22451 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____22451 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____22452, uu____22453) ->
                  let head1 =
                    let uu____22477 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22477
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22523 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22523
                      FStar_Pervasives_Native.fst in
                  ((let uu____22569 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22569
                    then
                      let uu____22570 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22571 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22572 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22570 uu____22571 uu____22572
                    else ());
                   (let no_free_uvars t =
                      (let uu____22582 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22582) &&
                        (let uu____22586 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22586) in
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
                      let uu____22602 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22602 = FStar_Syntax_Util.Equal in
                    let uu____22603 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22603
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22604 = equal t1 t2 in
                         (if uu____22604
                          then
                            let uu____22605 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22605
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22608 =
                            let uu____22615 = equal t1 t2 in
                            if uu____22615
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22625 = mk_eq2 wl env orig t1 t2 in
                               match uu____22625 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22608 with
                          | (guard, wl1) ->
                              let uu____22646 = solve_prob orig guard [] wl1 in
                              solve env uu____22646))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____22648, uu____22649) ->
                  let head1 =
                    let uu____22657 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22657
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22703 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22703
                      FStar_Pervasives_Native.fst in
                  ((let uu____22749 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22749
                    then
                      let uu____22750 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22751 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22752 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22750 uu____22751 uu____22752
                    else ());
                   (let no_free_uvars t =
                      (let uu____22762 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22762) &&
                        (let uu____22766 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22766) in
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
                      let uu____22782 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22782 = FStar_Syntax_Util.Equal in
                    let uu____22783 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22783
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22784 = equal t1 t2 in
                         (if uu____22784
                          then
                            let uu____22785 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22785
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22788 =
                            let uu____22795 = equal t1 t2 in
                            if uu____22795
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22805 = mk_eq2 wl env orig t1 t2 in
                               match uu____22805 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22788 with
                          | (guard, wl1) ->
                              let uu____22826 = solve_prob orig guard [] wl1 in
                              solve env uu____22826))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____22828, uu____22829) ->
                  let head1 =
                    let uu____22831 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22831
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22877 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22877
                      FStar_Pervasives_Native.fst in
                  ((let uu____22923 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22923
                    then
                      let uu____22924 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22925 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22926 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22924 uu____22925 uu____22926
                    else ());
                   (let no_free_uvars t =
                      (let uu____22936 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22936) &&
                        (let uu____22940 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22940) in
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
                      let uu____22956 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22956 = FStar_Syntax_Util.Equal in
                    let uu____22957 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22957
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22958 = equal t1 t2 in
                         (if uu____22958
                          then
                            let uu____22959 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22959
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22962 =
                            let uu____22969 = equal t1 t2 in
                            if uu____22969
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22979 = mk_eq2 wl env orig t1 t2 in
                               match uu____22979 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22962 with
                          | (guard, wl1) ->
                              let uu____23000 = solve_prob orig guard [] wl1 in
                              solve env uu____23000))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____23002, uu____23003) ->
                  let head1 =
                    let uu____23005 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23005
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23051 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23051
                      FStar_Pervasives_Native.fst in
                  ((let uu____23097 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23097
                    then
                      let uu____23098 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23099 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23100 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23098 uu____23099 uu____23100
                    else ());
                   (let no_free_uvars t =
                      (let uu____23110 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23110) &&
                        (let uu____23114 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23114) in
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
                      let uu____23130 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23130 = FStar_Syntax_Util.Equal in
                    let uu____23131 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23131
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23132 = equal t1 t2 in
                         (if uu____23132
                          then
                            let uu____23133 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23133
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23136 =
                            let uu____23143 = equal t1 t2 in
                            if uu____23143
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23153 = mk_eq2 wl env orig t1 t2 in
                               match uu____23153 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23136 with
                          | (guard, wl1) ->
                              let uu____23174 = solve_prob orig guard [] wl1 in
                              solve env uu____23174))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____23176, uu____23177) ->
                  let head1 =
                    let uu____23179 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23179
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23219 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23219
                      FStar_Pervasives_Native.fst in
                  ((let uu____23259 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23259
                    then
                      let uu____23260 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23261 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23262 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23260 uu____23261 uu____23262
                    else ());
                   (let no_free_uvars t =
                      (let uu____23272 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23272) &&
                        (let uu____23276 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23276) in
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
                      let uu____23292 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23292 = FStar_Syntax_Util.Equal in
                    let uu____23293 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23293
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23294 = equal t1 t2 in
                         (if uu____23294
                          then
                            let uu____23295 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23295
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23298 =
                            let uu____23305 = equal t1 t2 in
                            if uu____23305
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23315 = mk_eq2 wl env orig t1 t2 in
                               match uu____23315 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23298 with
                          | (guard, wl1) ->
                              let uu____23336 = solve_prob orig guard [] wl1 in
                              solve env uu____23336))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____23338, uu____23339) ->
                  let head1 =
                    let uu____23357 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23357
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23397 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23397
                      FStar_Pervasives_Native.fst in
                  ((let uu____23437 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23437
                    then
                      let uu____23438 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23439 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23440 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23438 uu____23439 uu____23440
                    else ());
                   (let no_free_uvars t =
                      (let uu____23450 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23450) &&
                        (let uu____23454 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23454) in
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
                      let uu____23470 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23470 = FStar_Syntax_Util.Equal in
                    let uu____23471 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23471
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23472 = equal t1 t2 in
                         (if uu____23472
                          then
                            let uu____23473 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23473
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23476 =
                            let uu____23483 = equal t1 t2 in
                            if uu____23483
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23493 = mk_eq2 wl env orig t1 t2 in
                               match uu____23493 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23476 with
                          | (guard, wl1) ->
                              let uu____23514 = solve_prob orig guard [] wl1 in
                              solve env uu____23514))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23516, FStar_Syntax_Syntax.Tm_match uu____23517) ->
                  let head1 =
                    let uu____23541 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23541
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23581 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23581
                      FStar_Pervasives_Native.fst in
                  ((let uu____23621 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23621
                    then
                      let uu____23622 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23623 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23624 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23622 uu____23623 uu____23624
                    else ());
                   (let no_free_uvars t =
                      (let uu____23634 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23634) &&
                        (let uu____23638 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23638) in
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
                      let uu____23654 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23654 = FStar_Syntax_Util.Equal in
                    let uu____23655 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23655
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23656 = equal t1 t2 in
                         (if uu____23656
                          then
                            let uu____23657 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23657
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23660 =
                            let uu____23667 = equal t1 t2 in
                            if uu____23667
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23677 = mk_eq2 wl env orig t1 t2 in
                               match uu____23677 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23660 with
                          | (guard, wl1) ->
                              let uu____23698 = solve_prob orig guard [] wl1 in
                              solve env uu____23698))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23700, FStar_Syntax_Syntax.Tm_uinst uu____23701) ->
                  let head1 =
                    let uu____23709 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23709
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23749 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23749
                      FStar_Pervasives_Native.fst in
                  ((let uu____23789 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23789
                    then
                      let uu____23790 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23791 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23792 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23790 uu____23791 uu____23792
                    else ());
                   (let no_free_uvars t =
                      (let uu____23802 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23802) &&
                        (let uu____23806 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23806) in
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
                      let uu____23822 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23822 = FStar_Syntax_Util.Equal in
                    let uu____23823 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23823
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23824 = equal t1 t2 in
                         (if uu____23824
                          then
                            let uu____23825 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23825
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23828 =
                            let uu____23835 = equal t1 t2 in
                            if uu____23835
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23845 = mk_eq2 wl env orig t1 t2 in
                               match uu____23845 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23828 with
                          | (guard, wl1) ->
                              let uu____23866 = solve_prob orig guard [] wl1 in
                              solve env uu____23866))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23868, FStar_Syntax_Syntax.Tm_name uu____23869) ->
                  let head1 =
                    let uu____23871 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23871
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23911 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23911
                      FStar_Pervasives_Native.fst in
                  ((let uu____23951 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23951
                    then
                      let uu____23952 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23953 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23954 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23952 uu____23953 uu____23954
                    else ());
                   (let no_free_uvars t =
                      (let uu____23964 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23964) &&
                        (let uu____23968 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23968) in
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
                      let uu____23984 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23984 = FStar_Syntax_Util.Equal in
                    let uu____23985 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23985
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23986 = equal t1 t2 in
                         (if uu____23986
                          then
                            let uu____23987 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23987
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23990 =
                            let uu____23997 = equal t1 t2 in
                            if uu____23997
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24007 = mk_eq2 wl env orig t1 t2 in
                               match uu____24007 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23990 with
                          | (guard, wl1) ->
                              let uu____24028 = solve_prob orig guard [] wl1 in
                              solve env uu____24028))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24030, FStar_Syntax_Syntax.Tm_constant uu____24031) ->
                  let head1 =
                    let uu____24033 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24033
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24073 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24073
                      FStar_Pervasives_Native.fst in
                  ((let uu____24113 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24113
                    then
                      let uu____24114 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24115 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24116 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24114 uu____24115 uu____24116
                    else ());
                   (let no_free_uvars t =
                      (let uu____24126 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24126) &&
                        (let uu____24130 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24130) in
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
                      let uu____24146 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24146 = FStar_Syntax_Util.Equal in
                    let uu____24147 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24147
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24148 = equal t1 t2 in
                         (if uu____24148
                          then
                            let uu____24149 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24149
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24152 =
                            let uu____24159 = equal t1 t2 in
                            if uu____24159
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24169 = mk_eq2 wl env orig t1 t2 in
                               match uu____24169 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24152 with
                          | (guard, wl1) ->
                              let uu____24190 = solve_prob orig guard [] wl1 in
                              solve env uu____24190))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24192, FStar_Syntax_Syntax.Tm_fvar uu____24193) ->
                  let head1 =
                    let uu____24195 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24195
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24241 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24241
                      FStar_Pervasives_Native.fst in
                  ((let uu____24287 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24287
                    then
                      let uu____24288 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24289 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24290 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24288 uu____24289 uu____24290
                    else ());
                   (let no_free_uvars t =
                      (let uu____24300 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24300) &&
                        (let uu____24304 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24304) in
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
                      let uu____24320 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24320 = FStar_Syntax_Util.Equal in
                    let uu____24321 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24321
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24322 = equal t1 t2 in
                         (if uu____24322
                          then
                            let uu____24323 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24323
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24326 =
                            let uu____24333 = equal t1 t2 in
                            if uu____24333
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24343 = mk_eq2 wl env orig t1 t2 in
                               match uu____24343 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24326 with
                          | (guard, wl1) ->
                              let uu____24364 = solve_prob orig guard [] wl1 in
                              solve env uu____24364))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24366, FStar_Syntax_Syntax.Tm_app uu____24367) ->
                  let head1 =
                    let uu____24385 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24385
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24425 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24425
                      FStar_Pervasives_Native.fst in
                  ((let uu____24465 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24465
                    then
                      let uu____24466 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24467 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24468 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24466 uu____24467 uu____24468
                    else ());
                   (let no_free_uvars t =
                      (let uu____24478 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24478) &&
                        (let uu____24482 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24482) in
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
                      let uu____24498 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24498 = FStar_Syntax_Util.Equal in
                    let uu____24499 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24499
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24500 = equal t1 t2 in
                         (if uu____24500
                          then
                            let uu____24501 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24501
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24504 =
                            let uu____24511 = equal t1 t2 in
                            if uu____24511
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24521 = mk_eq2 wl env orig t1 t2 in
                               match uu____24521 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24504 with
                          | (guard, wl1) ->
                              let uu____24542 = solve_prob orig guard [] wl1 in
                              solve env uu____24542))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____24544,
                 FStar_Syntax_Syntax.Tm_let uu____24545) ->
                  let uu____24570 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____24570
                  then
                    let uu____24571 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____24571
                  else
                    (let uu____24573 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____24573 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____24574, uu____24575) ->
                  let uu____24588 =
                    let uu____24593 =
                      let uu____24594 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24595 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24596 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24597 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24594 uu____24595 uu____24596 uu____24597 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24593) in
                  FStar_Errors.raise_error uu____24588
                    t1.FStar_Syntax_Syntax.pos
              | (uu____24598, FStar_Syntax_Syntax.Tm_let uu____24599) ->
                  let uu____24612 =
                    let uu____24617 =
                      let uu____24618 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24619 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24620 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24621 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24618 uu____24619 uu____24620 uu____24621 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24617) in
                  FStar_Errors.raise_error uu____24612
                    t1.FStar_Syntax_Syntax.pos
              | uu____24622 ->
                  let uu____24627 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____24627 orig))))
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
          (let uu____24689 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____24689
           then
             let uu____24690 =
               let uu____24691 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____24691 in
             let uu____24692 =
               let uu____24693 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____24693 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____24690 uu____24692
           else ());
          (let uu____24695 =
             let uu____24696 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____24696 in
           if uu____24695
           then
             let uu____24697 =
               mklstr
                 (fun uu____24704 ->
                    let uu____24705 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____24706 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____24705 uu____24706) in
             giveup env uu____24697 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____24724 =
                  mklstr
                    (fun uu____24731 ->
                       let uu____24732 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____24733 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____24732 uu____24733) in
                giveup env uu____24724 orig)
             else
               (let uu____24735 =
                  FStar_List.fold_left2
                    (fun uu____24756 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____24756 with
                           | (univ_sub_probs, wl1) ->
                               let uu____24777 =
                                 let uu____24782 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____24783 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____24782
                                   FStar_TypeChecker_Common.EQ uu____24783
                                   "effect universes" in
                               (match uu____24777 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____24735 with
                | (univ_sub_probs, wl1) ->
                    let uu____24802 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____24802 with
                     | (ret_sub_prob, wl2) ->
                         let uu____24809 =
                           FStar_List.fold_right2
                             (fun uu____24846 ->
                                fun uu____24847 ->
                                  fun uu____24848 ->
                                    match (uu____24846, uu____24847,
                                            uu____24848)
                                    with
                                    | ((a1, uu____24892), (a2, uu____24894),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____24927 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____24927 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____24809 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____24953 =
                                  let uu____24956 =
                                    let uu____24959 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____24959 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____24956 in
                                FStar_List.append univ_sub_probs uu____24953 in
                              let guard =
                                let guard =
                                  let uu____24978 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____24978 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3627_24987 = wl3 in
                                {
                                  attempting = (uu___3627_24987.attempting);
                                  wl_deferred = (uu___3627_24987.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3627_24987.wl_deferred_to_tac);
                                  ctr = (uu___3627_24987.ctr);
                                  defer_ok = (uu___3627_24987.defer_ok);
                                  smt_ok = (uu___3627_24987.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3627_24987.umax_heuristic_ok);
                                  tcenv = (uu___3627_24987.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3627_24987.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____24989 = attempt sub_probs wl5 in
                              solve env uu____24989)))) in
        let solve_layered_sub c11 c21 =
          (let uu____25002 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____25002
           then
             let uu____25003 =
               let uu____25004 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25004
                 FStar_Syntax_Print.comp_to_string in
             let uu____25005 =
               let uu____25006 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25006
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____25003 uu____25005
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____25011 =
                 let uu____25012 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25012 FStar_Ident.string_of_id in
               let uu____25013 =
                 let uu____25014 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25014 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____25011 uu____25013 in
             let lift_c1 edge =
               let uu____25029 =
                 let uu____25034 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____25034
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____25029
                 (fun uu____25051 ->
                    match uu____25051 with
                    | (c, g) ->
                        let uu____25062 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____25062, g)) in
             let uu____25063 =
               let uu____25074 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____25074 with
               | FStar_Pervasives_Native.None ->
                   let uu____25087 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____25087 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____25103 = lift_c1 edge in
                        (match uu____25103 with
                         | (c12, g_lift) ->
                             let uu____25120 =
                               let uu____25123 =
                                 let uu____25124 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____25124
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____25123
                                 (fun ts ->
                                    let uu____25130 =
                                      let uu____25131 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____25131
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____25130
                                      (fun uu____25142 ->
                                         FStar_Pervasives_Native.Some
                                           uu____25142)) in
                             (c12, g_lift, uu____25120, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____25146 =
                     let uu____25149 =
                       let uu____25150 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____25150
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____25149
                       (fun uu____25161 ->
                          FStar_Pervasives_Native.Some uu____25161) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____25146,
                     true) in
             match uu____25063 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____25172 =
                     mklstr
                       (fun uu____25179 ->
                          let uu____25180 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____25181 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____25180 uu____25181) in
                   giveup env uu____25172 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3662_25187 = wl in
                      {
                        attempting = (uu___3662_25187.attempting);
                        wl_deferred = (uu___3662_25187.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3662_25187.wl_deferred_to_tac);
                        ctr = (uu___3662_25187.ctr);
                        defer_ok = (uu___3662_25187.defer_ok);
                        smt_ok = (uu___3662_25187.smt_ok);
                        umax_heuristic_ok =
                          (uu___3662_25187.umax_heuristic_ok);
                        tcenv = (uu___3662_25187.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3662_25187.repr_subcomp_allowed)
                      } in
                    let uu____25188 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____25210 =
                             let uu____25211 = FStar_Syntax_Subst.compress t in
                             uu____25211.FStar_Syntax_Syntax.n in
                           match uu____25210 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____25214 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____25228)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____25234) ->
                               is_uvar t1
                           | uu____25259 -> false in
                         FStar_List.fold_right2
                           (fun uu____25292 ->
                              fun uu____25293 ->
                                fun uu____25294 ->
                                  match (uu____25292, uu____25293,
                                          uu____25294)
                                  with
                                  | ((a1, uu____25338), (a2, uu____25340),
                                     (is_sub_probs, wl2)) ->
                                      let uu____25373 = is_uvar a1 in
                                      if uu____25373
                                      then
                                        ((let uu____25381 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____25381
                                          then
                                            let uu____25382 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____25383 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____25382 uu____25383
                                          else ());
                                         (let uu____25385 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____25385 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____25188 with
                    | (is_sub_probs, wl2) ->
                        let uu____25411 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____25411 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____25424 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____25425 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____25424 s uu____25425 in
                             let uu____25426 =
                               let uu____25455 =
                                 let uu____25456 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____25456.FStar_Syntax_Syntax.n in
                               match uu____25455 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____25515 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____25515 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____25578 =
                                          let uu____25597 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____25597
                                            (fun uu____25700 ->
                                               match uu____25700 with
                                               | (l1, l2) ->
                                                   let uu____25773 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____25773)) in
                                        (match uu____25578 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____25878 ->
                                   let uu____25879 =
                                     let uu____25884 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____25884) in
                                   FStar_Errors.raise_error uu____25879 r in
                             (match uu____25426 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____25957 =
                                    let uu____25964 =
                                      let uu____25965 =
                                        let uu____25966 =
                                          let uu____25973 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____25973,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____25966 in
                                      [uu____25965] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____25964
                                      (fun b ->
                                         let uu____25989 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____25990 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____25991 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____25989 uu____25990
                                           uu____25991) r in
                                  (match uu____25957 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3727_25999 = wl3 in
                                         {
                                           attempting =
                                             (uu___3727_25999.attempting);
                                           wl_deferred =
                                             (uu___3727_25999.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3727_25999.wl_deferred_to_tac);
                                           ctr = (uu___3727_25999.ctr);
                                           defer_ok =
                                             (uu___3727_25999.defer_ok);
                                           smt_ok = (uu___3727_25999.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3727_25999.umax_heuristic_ok);
                                           tcenv = (uu___3727_25999.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3727_25999.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____26024 =
                                                  let uu____26031 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____26031, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____26024) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____26048 =
                                         let f_sort_is =
                                           let uu____26058 =
                                             let uu____26061 =
                                               let uu____26062 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____26062.FStar_Syntax_Syntax.sort in
                                             let uu____26071 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____26072 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____26061 uu____26071 r
                                               uu____26072 in
                                           FStar_All.pipe_right uu____26058
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____26077 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____26113 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____26113 with
                                                  | (ps, wl5) ->
                                                      ((let uu____26135 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____26135
                                                        then
                                                          let uu____26136 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____26137 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____26136
                                                            uu____26137
                                                        else ());
                                                       (let uu____26139 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____26139
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____26077 in
                                       (match uu____26048 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____26163 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____26163
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____26164 =
                                              let g_sort_is =
                                                let uu____26174 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____26175 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____26174 r uu____26175 in
                                              let uu____26176 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____26212 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____26212 with
                                                       | (ps, wl6) ->
                                                           ((let uu____26234
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____26234
                                                             then
                                                               let uu____26235
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____26236
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____26235
                                                                 uu____26236
                                                             else ());
                                                            (let uu____26238
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____26238
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____26176 in
                                            (match uu____26164 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____26264 =
                                                     let uu____26269 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____26270 =
                                                       let uu____26271 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____26271 in
                                                     (uu____26269,
                                                       uu____26270) in
                                                   match uu____26264 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____26299 =
                                                     let uu____26302 =
                                                       let uu____26305 =
                                                         let uu____26308 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____26308 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____26305 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____26302 in
                                                   ret_sub_prob ::
                                                     uu____26299 in
                                                 let guard =
                                                   let guard =
                                                     let uu____26329 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____26329 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____26340 =
                                                     let uu____26343 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____26346 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____26346)
                                                       uu____26343 in
                                                   solve_prob orig
                                                     uu____26340 [] wl6 in
                                                 let uu____26347 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____26347))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____26372 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____26374 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____26374]
               | x -> x in
             let c12 =
               let uu___3785_26377 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3785_26377.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3785_26377.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3785_26377.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3785_26377.FStar_Syntax_Syntax.flags)
               } in
             let uu____26378 =
               let uu____26383 =
                 FStar_All.pipe_right
                   (let uu___3788_26385 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3788_26385.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3788_26385.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3788_26385.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3788_26385.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____26383
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____26378
               (fun uu____26399 ->
                  match uu____26399 with
                  | (c, g) ->
                      let uu____26406 =
                        let uu____26407 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____26407 in
                      if uu____26406
                      then
                        let uu____26408 =
                          let uu____26413 =
                            let uu____26414 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____26415 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____26414 uu____26415 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____26413) in
                        FStar_Errors.raise_error uu____26408 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____26417 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____26419 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____26419))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____26417
           then
             let uu____26420 =
               mklstr
                 (fun uu____26427 ->
                    let uu____26428 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____26429 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____26428 uu____26429) in
             giveup env uu____26420 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_26435 ->
                        match uu___29_26435 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____26436 -> false)) in
              let uu____26437 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____26467)::uu____26468,
                   (wp2, uu____26470)::uu____26471) -> (wp1, wp2)
                | uu____26544 ->
                    let uu____26569 =
                      let uu____26574 =
                        let uu____26575 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____26576 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____26575 uu____26576 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____26574) in
                    FStar_Errors.raise_error uu____26569
                      env.FStar_TypeChecker_Env.range in
              match uu____26437 with
              | (wpc1, wpc2) ->
                  let uu____26583 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____26583
                  then
                    let uu____26584 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____26584 wl
                  else
                    (let uu____26586 =
                       let uu____26593 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____26593 in
                     match uu____26586 with
                     | (c2_decl, qualifiers) ->
                         let uu____26614 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____26614
                         then
                           let c1_repr =
                             let uu____26618 =
                               let uu____26619 =
                                 let uu____26620 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____26620 in
                               let uu____26621 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26619 uu____26621 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26618 in
                           let c2_repr =
                             let uu____26623 =
                               let uu____26624 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____26625 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26624 uu____26625 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26623 in
                           let uu____26626 =
                             let uu____26631 =
                               let uu____26632 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____26633 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____26632 uu____26633 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____26631 in
                           (match uu____26626 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____26637 = attempt [prob] wl2 in
                                solve env uu____26637)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____26654 = lift_c1 () in
                                   FStar_All.pipe_right uu____26654
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____26676 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____26676
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____26680 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____26680 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____26686 =
                                       let uu____26687 =
                                         let uu____26704 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____26707 =
                                           let uu____26718 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____26718; wpc1_2] in
                                         (uu____26704, uu____26707) in
                                       FStar_Syntax_Syntax.Tm_app uu____26687 in
                                     FStar_Syntax_Syntax.mk uu____26686 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____26766 =
                                      let uu____26767 =
                                        let uu____26784 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____26787 =
                                          let uu____26798 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____26807 =
                                            let uu____26818 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____26818; wpc1_2] in
                                          uu____26798 :: uu____26807 in
                                        (uu____26784, uu____26787) in
                                      FStar_Syntax_Syntax.Tm_app uu____26767 in
                                    FStar_Syntax_Syntax.mk uu____26766 r)) in
                            (let uu____26872 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____26872
                             then
                               let uu____26873 =
                                 let uu____26874 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____26874 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____26873
                             else ());
                            (let uu____26876 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____26876 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____26884 =
                                     let uu____26887 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____26890 ->
                                          FStar_Pervasives_Native.Some
                                            uu____26890) uu____26887 in
                                   solve_prob orig uu____26884 [] wl1 in
                                 let uu____26891 = attempt [base_prob] wl2 in
                                 solve env uu____26891))))) in
        let uu____26892 = FStar_Util.physical_equality c1 c2 in
        if uu____26892
        then
          let uu____26893 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____26893
        else
          ((let uu____26896 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____26896
            then
              let uu____26897 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____26898 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____26897
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____26898
            else ());
           (let uu____26900 =
              let uu____26909 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____26912 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____26909, uu____26912) in
            match uu____26900 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____26930),
                    FStar_Syntax_Syntax.Total (t2, uu____26932)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____26949 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____26949 wl
                 | (FStar_Syntax_Syntax.GTotal uu____26950,
                    FStar_Syntax_Syntax.Total uu____26951) ->
                     let uu____26968 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____26968 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____26970),
                    FStar_Syntax_Syntax.Total (t2, uu____26972)) ->
                     let uu____26989 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____26989 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____26991),
                    FStar_Syntax_Syntax.GTotal (t2, uu____26993)) ->
                     let uu____27010 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27010 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27012),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27014)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____27031 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27031 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27033),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27035)) ->
                     let uu____27052 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____27052 orig
                 | (FStar_Syntax_Syntax.GTotal uu____27053,
                    FStar_Syntax_Syntax.Comp uu____27054) ->
                     let uu____27063 =
                       let uu___3912_27066 = problem in
                       let uu____27069 =
                         let uu____27070 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27070 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3912_27066.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27069;
                         FStar_TypeChecker_Common.relation =
                           (uu___3912_27066.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3912_27066.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3912_27066.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3912_27066.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3912_27066.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3912_27066.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3912_27066.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3912_27066.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27063 wl
                 | (FStar_Syntax_Syntax.Total uu____27071,
                    FStar_Syntax_Syntax.Comp uu____27072) ->
                     let uu____27081 =
                       let uu___3912_27084 = problem in
                       let uu____27087 =
                         let uu____27088 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27088 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3912_27084.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27087;
                         FStar_TypeChecker_Common.relation =
                           (uu___3912_27084.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3912_27084.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3912_27084.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3912_27084.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3912_27084.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3912_27084.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3912_27084.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3912_27084.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27081 wl
                 | (FStar_Syntax_Syntax.Comp uu____27089,
                    FStar_Syntax_Syntax.GTotal uu____27090) ->
                     let uu____27099 =
                       let uu___3924_27102 = problem in
                       let uu____27105 =
                         let uu____27106 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27106 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3924_27102.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3924_27102.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3924_27102.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27105;
                         FStar_TypeChecker_Common.element =
                           (uu___3924_27102.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3924_27102.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3924_27102.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3924_27102.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3924_27102.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3924_27102.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27099 wl
                 | (FStar_Syntax_Syntax.Comp uu____27107,
                    FStar_Syntax_Syntax.Total uu____27108) ->
                     let uu____27117 =
                       let uu___3924_27120 = problem in
                       let uu____27123 =
                         let uu____27124 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27124 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3924_27120.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3924_27120.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3924_27120.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27123;
                         FStar_TypeChecker_Common.element =
                           (uu___3924_27120.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3924_27120.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3924_27120.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3924_27120.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3924_27120.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3924_27120.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27117 wl
                 | (FStar_Syntax_Syntax.Comp uu____27125,
                    FStar_Syntax_Syntax.Comp uu____27126) ->
                     let uu____27127 =
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
                     if uu____27127
                     then
                       let uu____27128 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____27128 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27132 =
                            let uu____27137 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____27137
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27143 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____27144 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____27143, uu____27144)) in
                          match uu____27132 with
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
                           (let uu____27151 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____27151
                            then
                              let uu____27152 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____27153 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____27152 uu____27153
                            else ());
                           (let uu____27155 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____27155
                            then solve_layered_sub c12 c22
                            else
                              (let uu____27157 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____27157 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____27160 =
                                     mklstr
                                       (fun uu____27167 ->
                                          let uu____27168 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____27169 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____27168 uu____27169) in
                                   giveup env uu____27160 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____27176 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____27176 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____27217 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____27217 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____27235 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27263 ->
                match uu____27263 with
                | (u1, u2) ->
                    let uu____27270 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____27271 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____27270 uu____27271)) in
      FStar_All.pipe_right uu____27235 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial, [], (uu____27298, [])) when
          let uu____27323 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____27323 -> "{}"
      | uu____27324 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27347 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____27347
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____27367 =
              FStar_List.map
                (fun uu____27378 ->
                   match uu____27378 with
                   | (msg, x) ->
                       let uu____27385 =
                         let uu____27386 = prob_to_string env x in
                         Prims.op_Hat ": " uu____27386 in
                       Prims.op_Hat msg uu____27385) defs in
            FStar_All.pipe_right uu____27367 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____27390 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____27391 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____27392 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____27390 uu____27391 uu____27392 imps
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
                  let uu____27445 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____27445
                  then
                    let uu____27446 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____27447 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27446
                      (rel_to_string rel) uu____27447
                  else "TOP" in
                let uu____27449 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____27449 with
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
              let uu____27507 =
                let uu____27510 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____27513 ->
                     FStar_Pervasives_Native.Some uu____27513) uu____27510 in
              FStar_Syntax_Syntax.new_bv uu____27507 t1 in
            let uu____27514 =
              let uu____27519 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27519 in
            match uu____27514 with | (p, wl1) -> (p, x, wl1)
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
        (let uu____27590 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____27590
         then
           let uu____27591 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____27591
         else ());
        (let uu____27595 =
           FStar_Util.record_time (fun uu____27601 -> solve env probs) in
         match uu____27595 with
         | (sol, ms) ->
             ((let uu____27613 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____27613
               then
                 let uu____27614 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____27614
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____27627 =
                     FStar_Util.record_time
                       (fun uu____27633 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____27627 with
                    | ((), ms1) ->
                        ((let uu____27644 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____27644
                          then
                            let uu____27645 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____27645
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____27656 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____27656
                     then
                       let uu____27657 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____27657
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
          ((let uu____27681 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____27681
            then
              let uu____27682 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27682
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____27686 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____27686
             then
               let uu____27687 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27687
             else ());
            (let f2 =
               let uu____27690 =
                 let uu____27691 = FStar_Syntax_Util.unmeta f1 in
                 uu____27691.FStar_Syntax_Syntax.n in
               match uu____27690 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27695 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4044_27696 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4044_27696.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4044_27696.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4044_27696.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4044_27696.FStar_TypeChecker_Common.implicits)
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
            let uu____27747 =
              let uu____27748 =
                let uu____27749 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____27750 ->
                       FStar_TypeChecker_Common.NonTrivial uu____27750) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____27749;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____27748 in
            FStar_All.pipe_left
              (fun uu____27757 -> FStar_Pervasives_Native.Some uu____27757)
              uu____27747
let with_guard_no_simp :
  'uuuuuu27766 .
    'uuuuuu27766 ->
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
            let uu____27815 =
              let uu____27816 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____27817 ->
                     FStar_TypeChecker_Common.NonTrivial uu____27817) in
              {
                FStar_TypeChecker_Common.guard_f = uu____27816;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____27815
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
          (let uu____27847 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____27847
           then
             let uu____27848 = FStar_Syntax_Print.term_to_string t1 in
             let uu____27849 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____27848
               uu____27849
           else ());
          (let uu____27851 =
             let uu____27856 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____27856 in
           match uu____27851 with
           | (prob, wl) ->
               let g =
                 let uu____27864 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____27874 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____27864 in
               ((let uu____27896 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____27896
                 then
                   let uu____27897 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____27897
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
        let uu____27914 = try_teq true env t1 t2 in
        match uu____27914 with
        | FStar_Pervasives_Native.None ->
            ((let uu____27918 = FStar_TypeChecker_Env.get_range env in
              let uu____27919 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____27918 uu____27919);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____27926 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____27926
              then
                let uu____27927 = FStar_Syntax_Print.term_to_string t1 in
                let uu____27928 = FStar_Syntax_Print.term_to_string t2 in
                let uu____27929 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____27927
                  uu____27928 uu____27929
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
        (let uu____27949 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____27949
         then
           let uu____27950 = FStar_Syntax_Print.term_to_string t1 in
           let uu____27951 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____27950
             uu____27951
         else ());
        (let uu____27953 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____27953 with
         | (prob, x, wl) ->
             let g =
               let uu____27968 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____27978 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____27968 in
             ((let uu____28000 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____28000
               then
                 let uu____28001 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____28001
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____28006 =
                     let uu____28007 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____28007 g1 in
                   FStar_Pervasives_Native.Some uu____28006)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____28028 = FStar_TypeChecker_Env.get_range env in
          let uu____28029 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____28028 uu____28029
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
        (let uu____28054 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____28054
         then
           let uu____28055 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____28056 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28055 uu____28056
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28059 =
           let uu____28066 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28066 "sub_comp" in
         match uu____28059 with
         | (prob, wl) ->
             let wl1 =
               let uu___4117_28076 = wl in
               {
                 attempting = (uu___4117_28076.attempting);
                 wl_deferred = (uu___4117_28076.wl_deferred);
                 wl_deferred_to_tac = (uu___4117_28076.wl_deferred_to_tac);
                 ctr = (uu___4117_28076.ctr);
                 defer_ok = (uu___4117_28076.defer_ok);
                 smt_ok = (uu___4117_28076.smt_ok);
                 umax_heuristic_ok = (uu___4117_28076.umax_heuristic_ok);
                 tcenv = (uu___4117_28076.tcenv);
                 wl_implicits = (uu___4117_28076.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____28079 =
                 FStar_Util.record_time
                   (fun uu____28090 ->
                      let uu____28091 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____28101 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____28091) in
               match uu____28079 with
               | (r, ms) ->
                   ((let uu____28131 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____28131
                     then
                       let uu____28132 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____28133 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____28134 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28132 uu____28133
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28134
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
      fun uu____28163 ->
        match uu____28163 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28206 =
                 let uu____28211 =
                   let uu____28212 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____28213 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28212 uu____28213 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28211) in
               let uu____28214 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____28206 uu____28214) in
            let equiv v v' =
              let uu____28226 =
                let uu____28231 = FStar_Syntax_Subst.compress_univ v in
                let uu____28232 = FStar_Syntax_Subst.compress_univ v' in
                (uu____28231, uu____28232) in
              match uu____28226 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28255 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____28285 = FStar_Syntax_Subst.compress_univ v in
                      match uu____28285 with
                      | FStar_Syntax_Syntax.U_unif uu____28292 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28323 ->
                                    match uu____28323 with
                                    | (u, v') ->
                                        let uu____28332 = equiv v v' in
                                        if uu____28332
                                        then
                                          let uu____28335 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____28335 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____28351 -> [])) in
            let uu____28356 =
              let wl =
                let uu___4160_28360 = empty_worklist env in
                {
                  attempting = (uu___4160_28360.attempting);
                  wl_deferred = (uu___4160_28360.wl_deferred);
                  wl_deferred_to_tac = (uu___4160_28360.wl_deferred_to_tac);
                  ctr = (uu___4160_28360.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4160_28360.smt_ok);
                  umax_heuristic_ok = (uu___4160_28360.umax_heuristic_ok);
                  tcenv = (uu___4160_28360.tcenv);
                  wl_implicits = (uu___4160_28360.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4160_28360.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28378 ->
                      match uu____28378 with
                      | (lb, v) ->
                          let uu____28385 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____28385 with
                           | USolved wl1 -> ()
                           | uu____28387 -> fail lb v))) in
            let rec check_ineq uu____28397 =
              match uu____28397 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____28406) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____28433,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____28435,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____28448) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____28455, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____28463 -> false) in
            let uu____28468 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28483 ->
                      match uu____28483 with
                      | (u, v) ->
                          let uu____28490 = check_ineq (u, v) in
                          if uu____28490
                          then true
                          else
                            ((let uu____28493 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____28493
                              then
                                let uu____28494 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____28495 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____28494
                                  uu____28495
                              else ());
                             false))) in
            if uu____28468
            then ()
            else
              ((let uu____28499 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____28499
                then
                  ((let uu____28501 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28501);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28511 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28511))
                else ());
               (let uu____28521 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28521))
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
          let fail uu____28595 =
            match uu____28595 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4238_28620 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4238_28620.attempting);
              wl_deferred = (uu___4238_28620.wl_deferred);
              wl_deferred_to_tac = (uu___4238_28620.wl_deferred_to_tac);
              ctr = (uu___4238_28620.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4238_28620.umax_heuristic_ok);
              tcenv = (uu___4238_28620.tcenv);
              wl_implicits = (uu___4238_28620.wl_implicits);
              repr_subcomp_allowed = (uu___4238_28620.repr_subcomp_allowed)
            } in
          (let uu____28622 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____28622
           then
             let uu____28623 = FStar_Util.string_of_bool defer_ok in
             let uu____28624 = wl_to_string wl in
             let uu____28625 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____28623 uu____28624 uu____28625
           else ());
          (let g1 =
             let uu____28628 = solve_and_commit env wl fail in
             match uu____28628 with
             | FStar_Pervasives_Native.Some
                 (uu____28637::uu____28638, uu____28639, uu____28640) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4255_28670 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4255_28670.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4255_28670.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____28675 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____28687 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____28687
             then
               let uu____28688 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____28688
             else ());
            (let uu___4263_28690 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4263_28690.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4263_28690.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4263_28690.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4263_28690.FStar_TypeChecker_Common.implicits)
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
          (let uu____28765 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____28765
           then
             let uu____28766 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____28766
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4280_28770 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4280_28770.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4280_28770.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4280_28770.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4280_28770.FStar_TypeChecker_Common.implicits)
             } in
           let uu____28771 =
             let uu____28772 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____28772 in
           if uu____28771
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____28780 = FStar_TypeChecker_Env.get_range env in
                      let uu____28781 =
                        let uu____28782 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____28782 in
                      FStar_Errors.diag uu____28780 uu____28781)
                   else ();
                   (let vc1 =
                      let uu____28785 =
                        let uu____28788 =
                          let uu____28789 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____28789 in
                        FStar_Pervasives_Native.Some uu____28788 in
                      FStar_Profiling.profile
                        (fun uu____28791 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____28785 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____28793 = FStar_TypeChecker_Env.get_range env in
                       let uu____28794 =
                         let uu____28795 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____28795 in
                       FStar_Errors.diag uu____28793 uu____28794)
                    else ();
                    (let uu____28798 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____28798 "discharge_guard'" env vc1);
                    (let uu____28799 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____28799 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____28806 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____28807 =
                                 let uu____28808 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____28808 in
                               FStar_Errors.diag uu____28806 uu____28807)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____28813 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____28814 =
                                 let uu____28815 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____28815 in
                               FStar_Errors.diag uu____28813 uu____28814)
                            else ();
                            (let vcs =
                               let uu____28826 = FStar_Options.use_tactics () in
                               if uu____28826
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____28846 ->
                                      (let uu____28848 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____28849 -> ()) uu____28848);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____28892 ->
                                               match uu____28892 with
                                               | (env1, goal, opts) ->
                                                   let uu____28908 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____28908, opts)))))
                               else
                                 (let uu____28910 =
                                    let uu____28917 = FStar_Options.peek () in
                                    (env, vc2, uu____28917) in
                                  [uu____28910]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____28950 ->
                                     match uu____28950 with
                                     | (env1, goal, opts) ->
                                         let uu____28960 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____28960 with
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
                                                 (let uu____28967 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____28968 =
                                                    let uu____28969 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____28970 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____28969 uu____28970 in
                                                  FStar_Errors.diag
                                                    uu____28967 uu____28968)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____28973 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____28974 =
                                                    let uu____28975 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____28975 in
                                                  FStar_Errors.diag
                                                    uu____28973 uu____28974)
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
      let uu____28989 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____28989 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____28996 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____28996
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____29007 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____29007 with
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
        let uu____29033 = try_teq false env t1 t2 in
        match uu____29033 with
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
             let uu____29076 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____29076 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____29086 =
                   let uu____29087 = FStar_Syntax_Subst.compress t_norm in
                   uu____29087.FStar_Syntax_Syntax.n in
                 (match uu____29086 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____29093 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29093
                        (fun uu____29096 ->
                           FStar_Pervasives_Native.Some uu____29096)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____29098) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____29103 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29103
                        (fun uu____29106 ->
                           FStar_Pervasives_Native.Some uu____29106)
                  | uu____29107 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____29117 =
                      let uu____29118 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____29118 FStar_Util.is_none in
                    if uu____29117
                    then
                      let uu____29123 = imp_value imp in
                      match uu____29123 with
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
        let uu____29144 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____29144 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____29162 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____29162 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____29166 ->
                       let uu____29167 =
                         let uu____29168 = FStar_Syntax_Subst.compress r in
                         uu____29168.FStar_Syntax_Syntax.n in
                       (match uu____29167 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____29172)
                            -> unresolved ctx_u'
                        | uu____29189 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____29209 = acc in
              match uu____29209 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____29216 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____29216 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____29229 = hd in
                       (match uu____29229 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____29235 = unresolved ctx_u in
                               if uu____29235
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____29244 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____29244
                                       then
                                         let uu____29245 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____29245
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____29251 =
                                           teq_nosmt env1 t tm in
                                         match uu____29251 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4425_29260 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4425_29260.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4425_29260.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4425_29260.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4425_29260.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4425_29260.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4425_29260.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4425_29260.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4428_29262 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4428_29262.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4428_29262.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4428_29262.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____29263 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4433_29269 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4433_29269.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4433_29269.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4433_29269.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4433_29269.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4433_29269.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4433_29269.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4433_29269.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4433_29269.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4433_29269.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4433_29269.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4433_29269.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4433_29269.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4433_29269.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4433_29269.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4433_29269.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4433_29269.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4433_29269.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4433_29269.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4433_29269.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4433_29269.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4433_29269.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4433_29269.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4433_29269.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4433_29269.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4433_29269.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4433_29269.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4433_29269.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4433_29269.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4433_29269.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4433_29269.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4433_29269.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4433_29269.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4433_29269.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4433_29269.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4433_29269.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4433_29269.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4433_29269.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4438_29272 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4438_29272.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4438_29272.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4438_29272.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4438_29272.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4438_29272.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4438_29272.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4438_29272.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4438_29272.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4438_29272.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4438_29272.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4438_29272.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4438_29272.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4438_29272.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4438_29272.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4438_29272.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4438_29272.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4438_29272.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4438_29272.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4438_29272.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4438_29272.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4438_29272.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4438_29272.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4438_29272.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4438_29272.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4438_29272.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4438_29272.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4438_29272.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4438_29272.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4438_29272.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4438_29272.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4438_29272.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4438_29272.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____29275 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29275
                                     then
                                       let uu____29276 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____29277 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____29278 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____29279 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____29276 uu____29277 uu____29278
                                         reason uu____29279
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4444_29283 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____29290 =
                                               let uu____29299 =
                                                 let uu____29306 =
                                                   let uu____29307 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____29308 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____29309 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____29307 uu____29308
                                                     uu____29309 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____29306, r) in
                                               [uu____29299] in
                                             FStar_Errors.add_errors
                                               uu____29290);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____29323 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____29333 ->
                                                 let uu____29334 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____29335 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____29336 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____29334 uu____29335
                                                   reason uu____29336)) env2
                                           g1 true in
                                       match uu____29323 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4456_29338 = g in
            let uu____29339 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4456_29338.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4456_29338.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4456_29338.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4456_29338.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____29339
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____29351 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29351
       then
         let uu____29352 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____29352
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
      (let uu____29375 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29375
       then
         let uu____29376 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____29376
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____29380 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____29381 -> ()) uu____29380
       | imp::uu____29383 ->
           let uu____29386 =
             let uu____29391 =
               let uu____29392 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____29393 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____29392 uu____29393
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29391) in
           FStar_Errors.raise_error uu____29386
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29409 = teq env t1 t2 in
        force_trivial_guard env uu____29409
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29425 = teq_nosmt env t1 t2 in
        match uu____29425 with
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
          (let uu____29455 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____29455
           then
             let uu____29456 =
               let uu____29457 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____29457
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____29463 = FStar_Syntax_Print.term_to_string t1 in
             let uu____29464 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____29456
               uu____29463 uu____29464
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4494_29476 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4494_29476.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4494_29476.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4494_29476.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4494_29476.FStar_TypeChecker_Common.implicits)
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
        (let uu____29511 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29511
         then
           let uu____29512 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29513 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29512
             uu____29513
         else ());
        (let uu____29515 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29515 with
         | (prob, x, wl) ->
             let g =
               let uu____29534 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29544 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29534 in
             ((let uu____29566 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____29566
               then
                 let uu____29567 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____29568 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____29569 =
                   let uu____29570 = FStar_Util.must g in
                   guard_to_string env uu____29570 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29567 uu____29568 uu____29569
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
        let uu____29604 = check_subtyping env t1 t2 in
        match uu____29604 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29623 =
              let uu____29624 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____29624 g in
            FStar_Pervasives_Native.Some uu____29623
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29642 = check_subtyping env t1 t2 in
        match uu____29642 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29661 =
              let uu____29662 =
                let uu____29663 = FStar_Syntax_Syntax.mk_binder x in
                [uu____29663] in
              FStar_TypeChecker_Env.close_guard env uu____29662 g in
            FStar_Pervasives_Native.Some uu____29661
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____29700 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29700
         then
           let uu____29701 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29702 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____29701
             uu____29702
         else ());
        (let uu____29704 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29704 with
         | (prob, x, wl) ->
             let g =
               let uu____29719 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____29729 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29719 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____29754 =
                      let uu____29755 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____29755] in
                    FStar_TypeChecker_Env.close_guard env uu____29754 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29792 = subtype_nosmt env t1 t2 in
        match uu____29792 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)