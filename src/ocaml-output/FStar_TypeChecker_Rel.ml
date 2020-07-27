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
                 | uu____5891 -> out) FStar_Syntax_Syntax.no_names g in
        let uu____5892 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____5956 ->
                  fun uu____5957 ->
                    match (uu____5956, uu____5957) with
                    | ((isect, isect_set), (x, imp)) ->
                        let uu____6060 =
                          let uu____6061 = FStar_Util.set_mem x v1_set in
                          FStar_All.pipe_left Prims.op_Negation uu____6061 in
                        if uu____6060
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6090 =
                             FStar_Util.set_is_subset_of fvs isect_set in
                           if uu____6090
                           then
                             let uu____6105 = FStar_Util.set_add x isect_set in
                             (((x, imp) :: isect), uu____6105)
                           else (isect, isect_set))) ([], ctx_binders)) in
        match uu____5892 with | (isect, uu____6154) -> FStar_List.rev isect
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt ->
    fun xs ->
      fun src ->
        fun wl ->
          let uu____6201 =
            maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
              src.FStar_Syntax_Syntax.ctx_uvar_binders in
          match uu____6201 with
          | (pfx, (tgt_sfx, src_sfx)) ->
              let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx in
              let xs_i = intersect_binders g src_sfx xs in
              let new_typ =
                let uu____6224 =
                  FStar_Syntax_Syntax.mk_Total
                    src.FStar_Syntax_Syntax.ctx_uvar_typ in
                FStar_Syntax_Util.arrow xs_i uu____6224 in
              let uu____6227 =
                let uu____6234 =
                  let uu____6235 =
                    FStar_Syntax_Print.uvar_to_string
                      src.FStar_Syntax_Syntax.ctx_uvar_head in
                  Prims.op_Hat "restricted " uu____6235 in
                new_uvar uu____6234 wl src.FStar_Syntax_Syntax.ctx_uvar_range
                  g pfx new_typ src.FStar_Syntax_Syntax.ctx_uvar_should_check
                  src.FStar_Syntax_Syntax.ctx_uvar_meta in
              (match uu____6227 with
               | (uu____6236, src', wl1) ->
                   let xs_args =
                     let uu____6240 =
                       FStar_Syntax_Syntax.binders_to_names xs_i in
                     FStar_List.map FStar_Syntax_Syntax.as_arg uu____6240 in
                   let uvar_app =
                     FStar_Syntax_Syntax.mk_Tm_app src' xs_args
                       src.FStar_Syntax_Syntax.ctx_uvar_range in
                   (FStar_Syntax_Util.set_uvar
                      src.FStar_Syntax_Syntax.ctx_uvar_head uvar_app;
                    wl1))
let (restrict_all_uvars :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list ->
      FStar_Syntax_Syntax.binders -> worklist -> worklist)
  =
  fun tgt ->
    fun sources ->
      fun xs ->
        fun wl -> FStar_List.fold_right (restrict_ctx tgt xs) sources wl
let binders_eq :
  'uuuuuu6285 'uuuuuu6286 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6285) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6286) Prims.list -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6343 ->
              fun uu____6344 ->
                match (uu____6343, uu____6344) with
                | ((a, uu____6362), (b, uu____6364)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let name_exists_in_binders :
  'uuuuuu6379 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6379) Prims.list -> Prims.bool
  =
  fun x ->
    fun bs ->
      FStar_Util.for_some
        (fun uu____6409 ->
           match uu____6409 with
           | (y, uu____6415) -> FStar_Syntax_Syntax.bv_eq x y) bs
let pat_vars :
  'uuuuuu6424 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6424) Prims.list ->
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
                   let uu____6586 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu____6586
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6616 -> FStar_Pervasives_Native.None) in
        aux [] args
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu____6663 -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch _0 -> true | uu____6700 -> false
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee -> match projectee with | HeadMatch _0 -> _0
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | FullMatch -> true | uu____6712 -> false
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_6717 ->
    match uu___19_6717 with
    | MisMatch (d1, d2) ->
        let uu____6728 =
          let uu____6729 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu____6730 =
            let uu____6731 =
              let uu____6732 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.op_Hat uu____6732 ")" in
            Prims.op_Hat ") (" uu____6731 in
          Prims.op_Hat uu____6729 uu____6730 in
        Prims.op_Hat "MisMatch (" uu____6728
    | HeadMatch u ->
        let uu____6734 = FStar_Util.string_of_bool u in
        Prims.op_Hat "HeadMatch " uu____6734
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___20_6739 ->
    match uu___20_6739 with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu____6754 -> HeadMatch false
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____6767 =
            (let uu____6772 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
             let uu____6773 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu____6772 = uu____6773) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) in
          if uu____6767 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____6776 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6776 with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6787 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6810 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6819 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6837 = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu____6837
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6838 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6839 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6840 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6853 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6866 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____6890) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____6896, uu____6897) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu____6939) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6964;
             FStar_Syntax_Syntax.index = uu____6965;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____6967)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6974 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6975 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6976 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6991 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6998 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7018 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____7018
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
           { FStar_Syntax_Syntax.blob = uu____7036;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7037;
             FStar_Syntax_Syntax.ltyp = uu____7038;
             FStar_Syntax_Syntax.rng = uu____7039;_},
           uu____7040) ->
            let uu____7051 = FStar_Syntax_Util.unlazy t11 in
            head_matches env uu____7051 t21
        | (uu____7052, FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7053;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7054;
             FStar_Syntax_Syntax.ltyp = uu____7055;
             FStar_Syntax_Syntax.rng = uu____7056;_})
            ->
            let uu____7067 = FStar_Syntax_Util.unlazy t21 in
            head_matches env t11 uu____7067
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7070 = FStar_Syntax_Syntax.bv_eq x y in
            if uu____7070
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7078 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____7078
            then FullMatch
            else
              (let uu____7080 =
                 let uu____7089 =
                   let uu____7092 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____7092 in
                 let uu____7093 =
                   let uu____7096 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____7096 in
                 (uu____7089, uu____7093) in
               MisMatch uu____7080)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu____7102),
           FStar_Syntax_Syntax.Tm_uinst (g, uu____7104)) ->
            let uu____7113 = head_matches env f g in
            FStar_All.pipe_right uu____7113 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           uu____7114) -> HeadMatch true
        | (uu____7115, FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify)) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7118 = FStar_Const.eq_const c d in
            if uu____7118
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu____7125),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu____7127)) ->
            let uu____7160 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head in
            if uu____7160
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7167),
           FStar_Syntax_Syntax.Tm_refine (y, uu____7169)) ->
            let uu____7178 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7178 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7180), uu____7181) ->
            let uu____7186 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____7186 head_match
        | (uu____7187, FStar_Syntax_Syntax.Tm_refine (x, uu____7189)) ->
            let uu____7194 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7194 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7195,
           FStar_Syntax_Syntax.Tm_type uu____7196) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow uu____7197,
           FStar_Syntax_Syntax.Tm_arrow uu____7198) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7228),
           FStar_Syntax_Syntax.Tm_app (head', uu____7230)) ->
            let uu____7279 = head_matches env head head' in
            FStar_All.pipe_right uu____7279 head_match
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7281), uu____7282) ->
            let uu____7307 = head_matches env head t21 in
            FStar_All.pipe_right uu____7307 head_match
        | (uu____7308, FStar_Syntax_Syntax.Tm_app (head, uu____7310)) ->
            let uu____7335 = head_matches env t11 head in
            FStar_All.pipe_right uu____7335 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7336, FStar_Syntax_Syntax.Tm_let
           uu____7337) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match uu____7362,
           FStar_Syntax_Syntax.Tm_match uu____7363) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7408, FStar_Syntax_Syntax.Tm_abs
           uu____7409) -> HeadMatch true
        | uu____7446 ->
            let uu____7451 =
              let uu____7460 = delta_depth_of_term env t11 in
              let uu____7463 = delta_depth_of_term env t21 in
              (uu____7460, uu____7463) in
            MisMatch uu____7451
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
              let uu____7531 = unrefine env t in
              FStar_Syntax_Util.head_of uu____7531 in
            (let uu____7533 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7533
             then
               let uu____7534 = FStar_Syntax_Print.term_to_string t in
               let uu____7535 = FStar_Syntax_Print.term_to_string head in
               FStar_Util.print2 "Head of %s is %s\n" uu____7534 uu____7535
             else ());
            (let uu____7537 =
               let uu____7538 = FStar_Syntax_Util.un_uinst head in
               uu____7538.FStar_Syntax_Syntax.n in
             match uu____7537 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7544 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 (match uu____7544 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu____7558 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta") in
                        if uu____7558
                        then
                          let uu____7559 =
                            FStar_Syntax_Print.term_to_string head in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7559
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7561 ->
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
                      let uu____7576 =
                        let uu____7577 = FStar_Syntax_Util.eq_tm t t' in
                        uu____7577 = FStar_Syntax_Util.Equal in
                      if uu____7576
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7582 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta") in
                          if uu____7582
                          then
                            let uu____7583 =
                              FStar_Syntax_Print.term_to_string t in
                            let uu____7584 =
                              FStar_Syntax_Print.term_to_string t' in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7583
                              uu____7584
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7586 -> FStar_Pervasives_Native.None) in
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
            (let uu____7724 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7724
             then
               let uu____7725 = FStar_Syntax_Print.term_to_string t11 in
               let uu____7726 = FStar_Syntax_Print.term_to_string t21 in
               let uu____7727 = string_of_match_result r in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7725
                 uu____7726 uu____7727
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
               let uu____7751 =
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
               match uu____7751 with
               | (t12, t22) -> aux retry (n_delta + Prims.int_one) t12 t22 in
             let reduce_both_and_try_again d r1 =
               let uu____7796 = FStar_TypeChecker_Common.decr_delta_depth d in
               match uu____7796 with
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
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7828),
                  uu____7829)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____7847 =
                      let uu____7856 = maybe_inline t11 in
                      let uu____7859 = maybe_inline t21 in
                      (uu____7856, uu____7859) in
                    match uu____7847 with
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
                 (uu____7896, FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7897))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____7915 =
                      let uu____7924 = maybe_inline t11 in
                      let uu____7927 = maybe_inline t21 in
                      (uu____7924, uu____7927) in
                    match uu____7915 with
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
             | MisMatch uu____7976 -> fail n_delta r t11 t21
             | uu____7985 -> success n_delta r t11 t21) in
          let r = aux true Prims.int_zero t1 t2 in
          (let uu____7998 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu____7998
           then
             let uu____7999 = FStar_Syntax_Print.term_to_string t1 in
             let uu____8000 = FStar_Syntax_Print.term_to_string t2 in
             let uu____8001 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             let uu____8008 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8020 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must in
                  FStar_All.pipe_right uu____8020
                    (fun uu____8054 ->
                       match uu____8054 with
                       | (t11, t21) ->
                           let uu____8061 =
                             FStar_Syntax_Print.term_to_string t11 in
                           let uu____8062 =
                             let uu____8063 =
                               FStar_Syntax_Print.term_to_string t21 in
                             Prims.op_Hat "; " uu____8063 in
                           Prims.op_Hat uu____8061 uu____8062)) in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____7999 uu____8000 uu____8001 uu____8008
           else ());
          r
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____8075 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____8075 FStar_Pervasives_Native.fst
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8088 ->
    match uu___21_8088 with
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
      let uu___1267_8125 = p in
      let uu____8128 = whnf tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8129 = whnf tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1267_8125.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8128;
        FStar_TypeChecker_Common.relation =
          (uu___1267_8125.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8129;
        FStar_TypeChecker_Common.element =
          (uu___1267_8125.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1267_8125.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1267_8125.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1267_8125.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1267_8125.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1267_8125.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8143 = compress_tprob tcenv p1 in
          FStar_All.pipe_right uu____8143
            (fun uu____8148 -> FStar_TypeChecker_Common.TProb uu____8148)
      | FStar_TypeChecker_Common.CProb uu____8149 -> p
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv ->
    fun pr ->
      let prob =
        let uu____8171 = compress_prob tcenv pr in
        FStar_All.pipe_right uu____8171 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8179 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8179 with
           | (lh, lhs_args) ->
               let uu____8226 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8226 with
                | (rh, rhs_args) ->
                    let uu____8273 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8286,
                         FStar_Syntax_Syntax.Tm_uvar uu____8287) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8376 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8403, uu____8404)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8419, FStar_Syntax_Syntax.Tm_uvar uu____8420)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8435,
                         FStar_Syntax_Syntax.Tm_arrow uu____8436) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1318_8466 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1318_8466.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1318_8466.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1318_8466.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1318_8466.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1318_8466.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1318_8466.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1318_8466.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1318_8466.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1318_8466.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8469,
                         FStar_Syntax_Syntax.Tm_type uu____8470) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1318_8486 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1318_8486.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1318_8486.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1318_8486.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1318_8486.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1318_8486.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1318_8486.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1318_8486.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1318_8486.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1318_8486.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type uu____8489,
                         FStar_Syntax_Syntax.Tm_uvar uu____8490) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1318_8506 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1318_8506.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1318_8506.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1318_8506.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1318_8506.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1318_8506.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1318_8506.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1318_8506.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1318_8506.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1318_8506.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8509, FStar_Syntax_Syntax.Tm_uvar uu____8510)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8525, uu____8526)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8541, FStar_Syntax_Syntax.Tm_uvar uu____8542)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8557, uu____8558) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu____8273 with
                     | (rank, tp1) ->
                         let uu____8571 =
                           FStar_All.pipe_right
                             (let uu___1338_8575 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1338_8575.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1338_8575.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1338_8575.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1338_8575.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1338_8575.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1338_8575.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1338_8575.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1338_8575.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1338_8575.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____8578 ->
                                FStar_TypeChecker_Common.TProb uu____8578) in
                         (rank, uu____8571))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8582 =
            FStar_All.pipe_right
              (let uu___1342_8586 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1342_8586.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1342_8586.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1342_8586.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1342_8586.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1342_8586.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1342_8586.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1342_8586.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1342_8586.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1342_8586.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____8589 -> FStar_TypeChecker_Common.CProb uu____8589) in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8582)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    let rec aux uu____8648 probs =
      match uu____8648 with
      | (min_rank, min, out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some p,
                   FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8729 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____8750 = rank wl.tcenv hd in
               (match uu____8750 with
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
                      (let uu____8809 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8813 = FStar_Option.get min_rank in
                            rank_less_than rank1 uu____8813) in
                       if uu____8809
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
          let uu____8881 = FStar_Syntax_Util.head_and_args t in
          match uu____8881 with
          | (hd, uu____8899) ->
              let uu____8924 =
                let uu____8925 = FStar_Syntax_Subst.compress hd in
                uu____8925.FStar_Syntax_Syntax.n in
              (match uu____8924 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu____8929) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____8963 ->
                           match uu____8963 with
                           | (y, uu____8971) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8993 ->
                                       match uu____8993 with
                                       | (x, uu____9001) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9006 -> false) in
        let uu____9007 = rank tcenv p in
        match uu____9007 with
        | (r, p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9014 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9046 -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | USolved _0 -> true | uu____9059 -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UFailed _0 -> true | uu____9072 -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s -> let uu____9084 = FStar_Thunk.mkv s in UFailed uu____9084
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu____9095 = mklstr s in UFailed uu____9095
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
                        let uu____9140 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____9140 with
                        | (k, uu____9146) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9158 -> false)))
            | uu____9159 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu____9211 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2 -> FStar_Syntax_Util.eq_univs uv1 uv2)) in
                        if uu____9211 then uv1 :: uvs else uvs) []) in
            let filter =
              FStar_List.filter
                (fun u ->
                   let uu____9231 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u' -> FStar_Syntax_Util.eq_univs u u')) in
                   Prims.op_Negation uu____9231) in
            let uu____9236 = filter u12 in
            let uu____9239 = filter u22 in (uu____9236, uu____9239) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9269 = filter_out_common_univs us1 us2 in
                   (match uu____9269 with
                    | (us11, us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13, u23::us23) ->
                                let uu____9328 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23 in
                                (match uu____9328 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9331 -> USolved wl1 in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9347 ->
                               let uu____9348 =
                                 FStar_Syntax_Print.univ_to_string u12 in
                               let uu____9349 =
                                 FStar_Syntax_Print.univ_to_string u22 in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9348 uu____9349))
               | (FStar_Syntax_Syntax.U_max us, u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9373 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9373 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | (u', FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9399 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9399 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | uu____9402 ->
                   ufailed_thunk
                     (fun uu____9413 ->
                        let uu____9414 =
                          FStar_Syntax_Print.univ_to_string u12 in
                        let uu____9415 =
                          FStar_Syntax_Print.univ_to_string u22 in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____9414 uu____9415 msg)) in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9416, uu____9417) ->
              let uu____9418 =
                let uu____9419 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9420 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9419 uu____9420 in
              failwith uu____9418
          | (FStar_Syntax_Syntax.U_unknown, uu____9421) ->
              let uu____9422 =
                let uu____9423 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9424 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9423 uu____9424 in
              failwith uu____9422
          | (uu____9425, FStar_Syntax_Syntax.U_bvar uu____9426) ->
              let uu____9427 =
                let uu____9428 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9429 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9428 uu____9429 in
              failwith uu____9427
          | (uu____9430, FStar_Syntax_Syntax.U_unknown) ->
              let uu____9431 =
                let uu____9432 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9433 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9432 uu____9433 in
              failwith uu____9431
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              let uu____9436 =
                let uu____9437 = FStar_Ident.string_of_id x in
                let uu____9438 = FStar_Ident.string_of_id y in
                uu____9437 = uu____9438 in
              if uu____9436
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9464 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9464
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu____9480 = occurs_univ v1 u3 in
              if uu____9480
              then
                let uu____9481 =
                  let uu____9482 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9483 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9482 uu____9483 in
                try_umax_components u11 u21 uu____9481
              else
                (let uu____9485 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9485)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9499 = occurs_univ v1 u3 in
              if uu____9499
              then
                let uu____9500 =
                  let uu____9501 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9502 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9501 uu____9502 in
                try_umax_components u11 u21 uu____9500
              else
                (let uu____9504 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9504)
          | (FStar_Syntax_Syntax.U_max uu____9505, uu____9506) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9512 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9512
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9514, FStar_Syntax_Syntax.U_max uu____9515) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9521 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9521
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9523,
             FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9524,
             FStar_Syntax_Syntax.U_name uu____9525) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ
             uu____9526) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name
             uu____9527) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9528,
             FStar_Syntax_Syntax.U_succ uu____9529) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9530,
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
      let uu____9630 = bc1 in
      match uu____9630 with
      | (bs1, mk_cod1) ->
          let uu____9674 = bc2 in
          (match uu____9674 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu____9785 = aux xs ys in
                     (match uu____9785 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu____9868 =
                       let uu____9875 = mk_cod1 xs in ([], uu____9875) in
                     let uu____9878 =
                       let uu____9885 = mk_cod2 ys in ([], uu____9885) in
                     (uu____9868, uu____9878) in
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
                  let uu____9953 = FStar_Syntax_Syntax.bv_to_name t in
                  FStar_Syntax_Util.mk_has_type t11 uu____9953 t21
              | FStar_Pervasives_Native.None ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11 in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11 in
                  let uu____9956 =
                    let uu____9957 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Util.mk_has_type t11 uu____9957 t21 in
                  FStar_Syntax_Util.mk_forall u_x x uu____9956 in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB ->
                let uu____9962 = has_type_guard t1 t2 in (uu____9962, wl)
            | FStar_TypeChecker_Common.SUBINV ->
                let uu____9963 = has_type_guard t2 t1 in (uu____9963, wl)
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_9968 ->
    match uu___22_9968 with
    | Flex (uu____9969, uu____9970, []) -> true
    | uu____9979 -> false
let (should_defer_flex_to_user_tac :
  FStar_TypeChecker_Env.env -> worklist -> flex_t -> Prims.bool) =
  fun env ->
    fun wl ->
      fun f ->
        let uu____9995 = f in
        match uu____9995 with
        | Flex (uu____9996, u, uu____9998) ->
            let b =
              FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                wl.tcenv u in
            ((let uu____10001 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ResolveImplicitsHook") in
              if uu____10001
              then
                let uu____10002 =
                  FStar_Syntax_Print.ctx_uvar_to_string_no_reason u in
                let uu____10003 = FStar_Util.string_of_bool b in
                FStar_Util.print2
                  "Rel.should_defer_flex_to_user_tac for %s returning %s\n"
                  uu____10002 uu____10003
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
      let uu____10027 = f in
      match uu____10027 with
      | Flex
          (uu____10034,
           { FStar_Syntax_Syntax.ctx_uvar_head = uu____10035;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10036;
             FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
             FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____10039;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____10040;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____10041;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____10042;_},
           args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10106 ->
                 match uu____10106 with
                 | (y, uu____10114) -> FStar_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu____10268 =
                  let uu____10283 =
                    let uu____10286 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10286 in
                  ((FStar_List.rev pat_binders), uu____10283) in
                FStar_Pervasives_Native.Some uu____10268
            | (uu____10319, []) ->
                let uu____10350 =
                  let uu____10365 =
                    let uu____10368 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10368 in
                  ((FStar_List.rev pat_binders), uu____10365) in
                FStar_Pervasives_Native.Some uu____10350
            | ((formal, formal_imp)::formals1, (a, a_imp)::args2) ->
                let uu____10459 =
                  let uu____10460 = FStar_Syntax_Subst.compress a in
                  uu____10460.FStar_Syntax_Syntax.n in
                (match uu____10459 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____10480 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders) in
                     if uu____10480
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1683_10507 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1683_10507.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1683_10507.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          } in
                        let subst =
                          let uu____10511 =
                            let uu____10512 =
                              let uu____10519 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              (formal, uu____10519) in
                            FStar_Syntax_Syntax.NT uu____10512 in
                          [uu____10511] in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1 in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res in
                        aux
                          (((let uu___1689_10535 = x1 in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1689_10535.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1689_10535.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10536 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([], args2) ->
                let uu____10576 =
                  let uu____10583 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStar_Syntax_Util.arrow_formals uu____10583 in
                (match uu____10576 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10642 ->
                          aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10667 ->
               let uu____10668 = FStar_Syntax_Util.arrow_formals t_hd in
               (match uu____10668 with
                | (formals, t_res) -> aux [] formals t_res args))
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu____10997 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel") in
       if uu____10997
       then
         let uu____10998 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____10998
       else ());
      (let uu____11001 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace") in
       if uu____11001
       then
         let uu____11002 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11002
       else ());
      (let uu____11004 = next_prob probs in
       match uu____11004 with
       | FStar_Pervasives_Native.Some (hd, tl, rank1) ->
           let probs1 =
             let uu___1716_11031 = probs in
             {
               attempting = tl;
               wl_deferred = (uu___1716_11031.wl_deferred);
               wl_deferred_to_tac = (uu___1716_11031.wl_deferred_to_tac);
               ctr = (uu___1716_11031.ctr);
               defer_ok = (uu___1716_11031.defer_ok);
               smt_ok = (uu___1716_11031.smt_ok);
               umax_heuristic_ok = (uu___1716_11031.umax_heuristic_ok);
               tcenv = (uu___1716_11031.tcenv);
               wl_implicits = (uu___1716_11031.wl_implicits);
               repr_subcomp_allowed = (uu___1716_11031.repr_subcomp_allowed)
             } in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11039 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs in
                 if uu____11039
                 then
                   let uu____11040 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                   solve env uu____11040
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
                           (let uu___1728_11045 = tp in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1728_11045.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1728_11045.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1728_11045.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1728_11045.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1728_11045.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1728_11045.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1728_11045.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1728_11045.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1728_11045.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None ->
           (match probs.wl_deferred with
            | [] ->
                let uu____11063 =
                  let uu____11070 = as_deferred probs.wl_deferred_to_tac in
                  ([], uu____11070, (probs.wl_implicits)) in
                Success uu____11063
            | uu____11075 ->
                let uu____11084 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11143 ->
                          match uu____11143 with
                          | (c, uu____11151, uu____11152) -> c < probs.ctr)) in
                (match uu____11084 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11193 =
                            let uu____11200 = as_deferred probs.wl_deferred in
                            let uu____11201 =
                              as_deferred probs.wl_deferred_to_tac in
                            (uu____11200, uu____11201, (probs.wl_implicits)) in
                          Success uu____11193
                      | uu____11202 ->
                          let uu____11211 =
                            let uu___1742_11212 = probs in
                            let uu____11213 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11232 ->
                                      match uu____11232 with
                                      | (uu____11239, uu____11240, y) -> y)) in
                            {
                              attempting = uu____11213;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1742_11212.wl_deferred_to_tac);
                              ctr = (uu___1742_11212.ctr);
                              defer_ok = (uu___1742_11212.defer_ok);
                              smt_ok = (uu___1742_11212.smt_ok);
                              umax_heuristic_ok =
                                (uu___1742_11212.umax_heuristic_ok);
                              tcenv = (uu___1742_11212.tcenv);
                              wl_implicits = (uu___1742_11212.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1742_11212.repr_subcomp_allowed)
                            } in
                          solve env uu____11211))))
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
            let uu____11247 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____11247 with
            | USolved wl1 ->
                let uu____11249 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____11249
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11252 = defer_lit "" orig wl1 in
                solve env uu____11252
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
                  let uu____11302 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____11302 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11305 -> ufailed_simple "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11317;
                  FStar_Syntax_Syntax.vars = uu____11318;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11321;
                  FStar_Syntax_Syntax.vars = uu____11322;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11334, uu____11335) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11342, FStar_Syntax_Syntax.Tm_uinst uu____11343) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11350 -> USolved wl
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
            ((let uu____11360 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____11360
              then
                let uu____11361 = prob_to_string env orig in
                let uu____11362 = FStar_Thunk.force msg in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11361 uu____11362
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
          let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
          let wl2 =
            let uu___1824_11371 = wl1 in
            let uu____11372 =
              let uu____11381 =
                let uu____11388 = FStar_Thunk.mkv reason in
                ((wl1.ctr), uu____11388, orig) in
              uu____11381 :: (wl1.wl_deferred_to_tac) in
            {
              attempting = (uu___1824_11371.attempting);
              wl_deferred = (uu___1824_11371.wl_deferred);
              wl_deferred_to_tac = uu____11372;
              ctr = (uu___1824_11371.ctr);
              defer_ok = (uu___1824_11371.defer_ok);
              smt_ok = (uu___1824_11371.smt_ok);
              umax_heuristic_ok = (uu___1824_11371.umax_heuristic_ok);
              tcenv = (uu___1824_11371.tcenv);
              wl_implicits = (uu___1824_11371.wl_implicits);
              repr_subcomp_allowed = (uu___1824_11371.repr_subcomp_allowed)
            } in
          solve env wl2
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
                let uu____11411 = FStar_Syntax_Util.head_and_args t in
                match uu____11411 with
                | (head, uu____11433) ->
                    let uu____11458 =
                      let uu____11459 = FStar_Syntax_Subst.compress head in
                      uu____11459.FStar_Syntax_Syntax.n in
                    (match uu____11458 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu____11467) ->
                         let uu____11484 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu____11484,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____11485 -> (false, "")) in
              let uu____11486 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu____11486 with
               | (l1, r1) ->
                   let uu____11493 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu____11493 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____11501 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl in
                           solve env uu____11501)))
          | uu____11502 ->
              let uu____11503 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu____11503
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
               let uu____11587 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu____11587 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu____11640 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu____11640
                then
                  let uu____11641 = FStar_Syntax_Print.term_to_string t1 in
                  let uu____11642 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____11641 uu____11642
                else ());
               (let uu____11644 = head_matches_delta env1 wl2 t1 t2 in
                match uu____11644 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu____11689 = eq_prob t1 t2 wl2 in
                         (match uu____11689 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11710 ->
                         let uu____11719 = eq_prob t1 t2 wl2 in
                         (match uu____11719 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu____11768 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu____11783 =
                                 FStar_Syntax_Subst.compress t11 in
                               let uu____11784 =
                                 FStar_Syntax_Subst.compress t21 in
                               (uu____11783, uu____11784)
                           | FStar_Pervasives_Native.None ->
                               let uu____11789 =
                                 FStar_Syntax_Subst.compress t1 in
                               let uu____11790 =
                                 FStar_Syntax_Subst.compress t2 in
                               (uu____11789, uu____11790) in
                         (match uu____11768 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11821 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu____11821 with
                                | (t1_hd, t1_args) ->
                                    let uu____11866 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu____11866 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11930 =
                                              let uu____11937 =
                                                let uu____11948 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu____11948 :: t1_args in
                                              let uu____11965 =
                                                let uu____11974 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu____11974 :: t2_args in
                                              FStar_List.fold_left2
                                                (fun uu____12023 ->
                                                   fun uu____12024 ->
                                                     fun uu____12025 ->
                                                       match (uu____12023,
                                                               uu____12024,
                                                               uu____12025)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu____12075),
                                                          (a2, uu____12077))
                                                           ->
                                                           let uu____12114 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu____12114
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11937
                                                uu____11965 in
                                            match uu____11930 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  let uu___1927_12140 = wl4 in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1927_12140.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1927_12140.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1927_12140.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1927_12140.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1927_12140.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____12148 =
                                                  solve env1 wl' in
                                                (match uu____12148 with
                                                 | Success
                                                     (uu____12151,
                                                      defer_to_tac, imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____12155 =
                                                         extend_wl wl4
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu____12155))
                                                 | Failed uu____12156 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu____12188 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu____12188 with
                                | (t1_base, p1_opt) ->
                                    let uu____12223 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu____12223 with
                                     | (t2_base, p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____12321 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu____12321
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
                                               let uu____12369 =
                                                 op phi11 phi21 in
                                               refine x1 uu____12369
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
                                               let uu____12399 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12399
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
                                               let uu____12429 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12429
                                           | uu____12432 -> t_base in
                                         let uu____12449 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu____12449 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____12463 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu____12463, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu____12470 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu____12470 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu____12505 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu____12505 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu____12540 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu____12540
                                                         with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu____12564 = combine t11 t21 wl2 in
                              (match uu____12564 with
                               | (t12, ps, wl3) ->
                                   ((let uu____12597 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu____12597
                                     then
                                       let uu____12598 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____12598
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu____12637 ts1 =
               match uu____12637 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12700 = pairwise out t wl2 in
                        (match uu____12700 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2)) in
             let uu____12736 =
               let uu____12747 = FStar_List.hd ts in (uu____12747, [], wl1) in
             let uu____12756 = FStar_List.tl ts in
             aux uu____12736 uu____12756 in
           let uu____12763 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu____12763 with
           | (this_flex, this_rigid) ->
               let uu____12787 =
                 let uu____12788 = FStar_Syntax_Subst.compress this_rigid in
                 uu____12788.FStar_Syntax_Syntax.n in
               (match uu____12787 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu____12813 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu____12813
                    then
                      let uu____12814 = destruct_flex_t this_flex wl in
                      (match uu____12814 with
                       | (flex, wl1) ->
                           let uu____12821 = quasi_pattern env flex in
                           (match uu____12821 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu____12839 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____12839
                                  then
                                    let uu____12840 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12840
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12843 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2037_12846 = tp in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2037_12846.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2037_12846.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2037_12846.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2037_12846.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2037_12846.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2037_12846.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2037_12846.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2037_12846.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2037_12846.FStar_TypeChecker_Common.rank)
                                }))] wl in
                       solve env uu____12843)
                | uu____12847 ->
                    ((let uu____12849 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____12849
                      then
                        let uu____12850 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12850
                      else ());
                     (let uu____12852 =
                        FStar_Syntax_Util.head_and_args this_flex in
                      match uu____12852 with
                      | (u, _args) ->
                          let uu____12895 =
                            let uu____12896 = FStar_Syntax_Subst.compress u in
                            uu____12896.FStar_Syntax_Syntax.n in
                          (match uu____12895 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu____12923 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu____12923 with
                                 | (u', uu____12941) ->
                                     let uu____12966 =
                                       let uu____12967 = whnf env u' in
                                       uu____12967.FStar_Syntax_Syntax.n in
                                     (match uu____12966 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12988 -> false) in
                               let uu____12989 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13012 ->
                                         match uu___23_13012 with
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
                                              | uu____13021 -> false)
                                         | uu____13024 -> false)) in
                               (match uu____12989 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu____13038 = whnf env this_rigid in
                                      let uu____13039 =
                                        FStar_List.collect
                                          (fun uu___24_13045 ->
                                             match uu___24_13045 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13051 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu____13051]
                                             | uu____13053 -> [])
                                          bounds_probs in
                                      uu____13038 :: uu____13039 in
                                    let uu____13054 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu____13054 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu____13085 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu____13100 =
                                               let uu____13101 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu____13101.FStar_Syntax_Syntax.n in
                                             match uu____13100 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13113 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13113)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13122 -> bound in
                                           let uu____13123 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu____13123) in
                                         (match uu____13085 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13152 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu____13152
                                                then
                                                  let wl'1 =
                                                    let uu___2097_13154 = wl1 in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2097_13154.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2097_13154.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2097_13154.ctr);
                                                      defer_ok =
                                                        (uu___2097_13154.defer_ok);
                                                      smt_ok =
                                                        (uu___2097_13154.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2097_13154.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2097_13154.tcenv);
                                                      wl_implicits =
                                                        (uu___2097_13154.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2097_13154.repr_subcomp_allowed)
                                                    } in
                                                  let uu____13155 =
                                                    wl_to_string wl'1 in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13155
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____13158 =
                                                  solve_t env eq_prob
                                                    (let uu___2102_13160 =
                                                       wl' in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2102_13160.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2102_13160.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2102_13160.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2102_13160.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2102_13160.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2102_13160.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2102_13160.repr_subcomp_allowed)
                                                     }) in
                                                match uu____13158 with
                                                | Success
                                                    (uu____13161,
                                                     defer_to_tac, imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2109_13165 =
                                                        wl' in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2109_13165.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2109_13165.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2109_13165.ctr);
                                                        defer_ok =
                                                          (uu___2109_13165.defer_ok);
                                                        smt_ok =
                                                          (uu___2109_13165.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2109_13165.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2109_13165.tcenv);
                                                        wl_implicits =
                                                          (uu___2109_13165.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2109_13165.repr_subcomp_allowed)
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
                                                    let uu____13181 =
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
                                                    ((let uu____13192 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu____13192
                                                      then
                                                        let uu____13193 =
                                                          let uu____13194 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_All.pipe_right
                                                            uu____13194
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13193
                                                      else ());
                                                     (let uu____13200 =
                                                        let uu____13215 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu____13215) in
                                                      match uu____13200 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu____13237)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13263 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13263
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
                                                                  let uu____13280
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13280))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13305 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13305
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
                                                                    let uu____13323
                                                                    =
                                                                    let uu____13328
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13328 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13323
                                                                    [] wl2 in
                                                                  let uu____13333
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13333))))
                                                      | uu____13334 ->
                                                          let uu____13349 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env
                                                            uu____13349 p)))))))
                           | uu____13352 when flip ->
                               let uu____13353 =
                                 let uu____13354 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13355 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13354 uu____13355 in
                               failwith uu____13353
                           | uu____13356 ->
                               let uu____13357 =
                                 let uu____13358 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13359 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13358 uu____13359 in
                               failwith uu____13357)))))
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
                      (fun uu____13393 ->
                         match uu____13393 with
                         | (x, i) ->
                             let uu____13412 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             (uu____13412, i)) bs_lhs in
                  let uu____13415 = lhs in
                  match uu____13415 with
                  | Flex (uu____13416, u_lhs, uu____13418) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____13515 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____13525 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu____13525, univ) in
                          match uu____13515 with
                          | (k, univ) ->
                              let uu____13532 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2 in
                              (match uu____13532 with
                               | (uu____13549, u, wl3) ->
                                   let uu____13552 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu____13552, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____13578 =
                              let uu____13591 =
                                let uu____13602 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu____13602 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_List.fold_right
                                (fun uu____13653 ->
                                   fun uu____13654 ->
                                     match (uu____13653, uu____13654) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu____13755 =
                                           let uu____13762 =
                                             let uu____13765 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13765 in
                                           copy_uvar u_lhs [] uu____13762 wl2 in
                                         (match uu____13755 with
                                          | (uu____13794, t_a, wl3) ->
                                              let uu____13797 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu____13797 with
                                               | (uu____13816, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____13591
                                ([], wl1) in
                            (match uu____13578 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_13885 ->
                                        match uu___25_13885 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____13886 -> false
                                        | uu____13889 -> true) flags in
                                 let ct' =
                                   let uu___2228_13891 = ct in
                                   let uu____13892 =
                                     let uu____13895 = FStar_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu____13895 in
                                   let uu____13910 = FStar_List.tl out_args in
                                   let uu____13927 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2228_13891.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2228_13891.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13892;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13910;
                                     FStar_Syntax_Syntax.flags = uu____13927
                                   } in
                                 ((let uu___2231_13931 = c in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2231_13931.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2231_13931.FStar_Syntax_Syntax.vars)
                                   }), wl2)) in
                      let uu____13934 =
                        FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu____13934 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13972 =
                                   imitate_comp bs bs_terms c wl1 in
                                 (match uu____13972 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu____13983 =
                                          let uu____13988 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____13988) in
                                        TERM uu____13983 in
                                      let uu____13989 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu____13989 with
                                       | (sub_prob, wl3) ->
                                           let uu____14002 =
                                             let uu____14003 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu____14003 in
                                           solve env uu____14002))
                             | (x, imp)::formals2 ->
                                 let uu____14025 =
                                   let uu____14032 =
                                     let uu____14035 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____14035
                                       FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14032 wl1 in
                                 (match uu____14025 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu____14056 =
                                          let uu____14059 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some
                                            uu____14059 in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14056 u_x in
                                      let uu____14060 =
                                        let uu____14063 =
                                          let uu____14066 =
                                            let uu____14067 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y in
                                            (uu____14067, imp) in
                                          [uu____14066] in
                                        FStar_List.append bs_terms
                                          uu____14063 in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14060 formals2 wl2) in
                           let uu____14094 = occurs_check u_lhs arrow in
                           (match uu____14094 with
                            | (uu____14105, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14116 =
                                    mklstr
                                      (fun uu____14121 ->
                                         let uu____14122 =
                                           FStar_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14122) in
                                  giveup_or_defer env orig wl uu____14116
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
              (let uu____14151 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____14151
               then
                 let uu____14152 =
                   FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu____14153 =
                   FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14152 (rel_to_string (p_rel orig)) uu____14153
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu____14278 = rhs wl1 scope env1 subst in
                     (match uu____14278 with
                      | (rhs_prob, wl2) ->
                          ((let uu____14300 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu____14300
                            then
                              let uu____14301 = prob_to_string env1 rhs_prob in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14301
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1, imp)::xs1, (hd2, imp')::ys1) when
                     let uu____14374 = FStar_Syntax_Util.eq_aqual imp imp' in
                     uu____14374 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2301_14376 = hd1 in
                       let uu____14377 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2301_14376.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2301_14376.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14377
                       } in
                     let hd21 =
                       let uu___2304_14381 = hd2 in
                       let uu____14382 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2304_14381.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2304_14381.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14382
                       } in
                     let uu____14385 =
                       let uu____14390 =
                         FStar_All.pipe_left invert_rel (p_rel orig) in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____14390
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter" in
                     (match uu____14385 with
                      | (prob, wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                          let subst1 =
                            let uu____14411 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____14411 in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                          let uu____14415 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1 in
                          (match uu____14415 with
                           | (env3, FStar_Util.Inl (sub_probs, phi), wl3) ->
                               let phi1 =
                                 let uu____14483 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____14483 in
                               ((let uu____14501 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14501
                                 then
                                   let uu____14502 =
                                     FStar_Syntax_Print.term_to_string phi1 in
                                   let uu____14503 =
                                     FStar_Syntax_Print.bv_to_string hd12 in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____14502
                                     uu____14503
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____14532 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1) in
               let uu____14565 = aux wl [] env [] bs1 bs2 in
               match uu____14565 with
               | (env1, FStar_Util.Inr msg, wl1) -> giveup_lit env1 msg orig
               | (env1, FStar_Util.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu____14618 = attempt sub_probs wl2 in
                   solve env1 uu____14618)
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
            let uu___2342_14638 = wl in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2342_14638.wl_deferred_to_tac);
              ctr = (uu___2342_14638.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2342_14638.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2342_14638.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu____14646 = try_solve env wl' in
          match uu____14646 with
          | Success (uu____14647, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____14659 = compress_tprob wl.tcenv problem in
         solve_t' env uu____14659 wl)
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
            let uu____14665 = should_defer_flex_to_user_tac env wl lhs in
            if uu____14665
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____14675 =
                   FStar_List.map FStar_Pervasives_Native.fst bs in
                 FStar_Util.as_set uu____14675 FStar_Syntax_Syntax.order_bv in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____14709 = lhs1 in
                 match uu____14709 with
                 | Flex (uu____14712, ctx_u, uu____14714) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____14722 ->
                           let uu____14723 = sn_binders env1 bs in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____14723 rhs1 in
                     [TERM (ctx_u, sol)] in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____14770 = quasi_pattern env1 lhs1 in
                 match uu____14770 with
                 | FStar_Pervasives_Native.None ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs, uu____14800) ->
                     let uu____14805 = lhs1 in
                     (match uu____14805 with
                      | Flex (t_lhs, ctx_u, args) ->
                          let uu____14819 = occurs_check ctx_u rhs1 in
                          (match uu____14819 with
                           | (uvars, occurs_ok, msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14861 =
                                   let uu____14868 =
                                     let uu____14869 = FStar_Option.get msg in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____14869 in
                                   FStar_Util.Inl uu____14868 in
                                 (uu____14861, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs) in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1 in
                                  let uu____14891 =
                                    let uu____14892 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs in
                                    Prims.op_Negation uu____14892 in
                                  if uu____14891
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____14912 =
                                       let uu____14919 =
                                         mk_solution env1 lhs1 bs rhs1 in
                                       FStar_Util.Inr uu____14919 in
                                     let uu____14924 =
                                       restrict_all_uvars ctx_u uvars [] wl1 in
                                     (uu____14912, uu____14924))))) in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____14973 = FStar_Syntax_Util.head_and_args rhs1 in
                 match uu____14973 with
                 | (rhs_hd, args) ->
                     let uu____15016 = FStar_Util.prefix args in
                     (match uu____15016 with
                      | (args_rhs, last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              rhs1.FStar_Syntax_Syntax.pos in
                          let uu____15086 = lhs1 in
                          (match uu____15086 with
                           | Flex (t_lhs, u_lhs, _lhs_args) ->
                               let uu____15090 =
                                 let uu____15101 =
                                   let uu____15108 =
                                     let uu____15111 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____15111 in
                                   copy_uvar u_lhs [] uu____15108 wl1 in
                                 match uu____15101 with
                                 | (uu____15138, t_last_arg, wl2) ->
                                     let uu____15141 =
                                       let uu____15148 =
                                         let uu____15149 =
                                           let uu____15158 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg in
                                           [uu____15158] in
                                         FStar_List.append bs_lhs uu____15149 in
                                       copy_uvar u_lhs uu____15148 t_res_lhs
                                         wl2 in
                                     (match uu____15141 with
                                      | (uu____15193, lhs', wl3) ->
                                          let uu____15196 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3 in
                                          (match uu____15196 with
                                           | (uu____15213, lhs'_last_arg,
                                              wl4) ->
                                               (lhs', lhs'_last_arg, wl4))) in
                               (match uu____15090 with
                                | (lhs', lhs'_last_arg, wl2) ->
                                    let sol =
                                      let uu____15234 =
                                        let uu____15235 =
                                          let uu____15240 =
                                            let uu____15241 =
                                              let uu____15244 =
                                                let uu____15245 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lhs'_last_arg in
                                                [uu____15245] in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                lhs' uu____15244
                                                t_lhs.FStar_Syntax_Syntax.pos in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____15241
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____15240) in
                                        TERM uu____15235 in
                                      [uu____15234] in
                                    let uu____15270 =
                                      let uu____15277 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs" in
                                      match uu____15277 with
                                      | (p1, wl3) ->
                                          let uu____15296 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs" in
                                          (match uu____15296 with
                                           | (p2, wl4) -> ([p1; p2], wl4)) in
                                    (match uu____15270 with
                                     | (sub_probs, wl3) ->
                                         let uu____15327 =
                                           let uu____15328 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3 in
                                           attempt sub_probs uu____15328 in
                                         solve env1 uu____15327)))) in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____15361 = FStar_Syntax_Util.head_and_args rhs2 in
                   match uu____15361 with
                   | (uu____15378, args) ->
                       (match args with | [] -> false | uu____15412 -> true) in
                 let is_arrow rhs2 =
                   let uu____15429 =
                     let uu____15430 = FStar_Syntax_Subst.compress rhs2 in
                     uu____15430.FStar_Syntax_Syntax.n in
                   match uu____15429 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____15433 -> true
                   | uu____15448 -> false in
                 let uu____15449 = quasi_pattern env1 lhs1 in
                 match uu____15449 with
                 | FStar_Pervasives_Native.None ->
                     let msg =
                       mklstr
                         (fun uu____15467 ->
                            let uu____15468 = prob_to_string env1 orig1 in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____15468) in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                     let uu____15475 = is_app rhs1 in
                     if uu____15475
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____15477 = is_arrow rhs1 in
                        if uu____15477
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____15486 ->
                                  let uu____15487 = prob_to_string env1 orig1 in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____15487) in
                           giveup_or_defer env1 orig1 wl1 msg)) in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB ->
                   if wl.defer_ok
                   then
                     let uu____15488 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____15488
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV ->
                   if wl.defer_ok
                   then
                     let uu____15490 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____15490
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ ->
                   let uu____15492 = lhs in
                   (match uu____15492 with
                    | Flex (_t1, ctx_uv, args_lhs) ->
                        let uu____15496 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs in
                        (match uu____15496 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs in
                             let names_to_string1 fvs =
                               let uu____15513 =
                                 let uu____15516 =
                                   FStar_Util.set_elements fvs in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____15516 in
                               FStar_All.pipe_right uu____15513
                                 (FStar_String.concat ", ") in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders) in
                             let fvs2 = FStar_Syntax_Free.names rhs1 in
                             let uu____15533 = occurs_check ctx_uv rhs1 in
                             (match uu____15533 with
                              | (uvars, occurs_ok, msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____15555 =
                                      let uu____15556 =
                                        let uu____15557 =
                                          FStar_Option.get msg in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____15557 in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____15556 in
                                    giveup_or_defer env orig wl uu____15555
                                  else
                                    (let uu____15559 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1 in
                                     if uu____15559
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1 in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars
                                           lhs_binders wl in
                                       let uu____15564 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1 in
                                       solve env uu____15564
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____15577 ->
                                                 let uu____15578 =
                                                   names_to_string1 fvs2 in
                                                 let uu____15579 =
                                                   names_to_string1 fvs1 in
                                                 let uu____15580 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders) in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____15578 uu____15579
                                                   uu____15580) in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____15588 ->
                             if wl.defer_ok
                             then
                               let uu____15591 =
                                 FStar_Thunk.mkv "Not a pattern" in
                               giveup_or_defer env orig wl uu____15591
                             else
                               (let uu____15593 =
                                  try_quasi_pattern orig env wl lhs rhs in
                                match uu____15593 with
                                | (FStar_Util.Inr sol, wl1) ->
                                    let uu____15616 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1 in
                                    solve env uu____15616
                                | (FStar_Util.Inl msg, uu____15618) ->
                                    first_order orig env wl lhs rhs))))
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
                  let uu____15632 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15632
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok
                then
                  let uu____15634 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15634
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu____15636 =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu____15636
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
                    (let uu____15638 =
                       FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer env orig wl uu____15638)
                  else
                    (let uu____15640 =
                       let uu____15657 = quasi_pattern env lhs in
                       let uu____15664 = quasi_pattern env rhs in
                       (uu____15657, uu____15664) in
                     match uu____15640 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs, t_res_lhs),
                        FStar_Pervasives_Native.Some
                        (binders_rhs, t_res_rhs)) ->
                         let uu____15707 = lhs in
                         (match uu____15707 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____15708;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____15710;_},
                               u_lhs, uu____15712)
                              ->
                              let uu____15715 = rhs in
                              (match uu____15715 with
                               | Flex (uu____15716, u_rhs, uu____15718) ->
                                   let uu____15719 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs) in
                                   if uu____15719
                                   then
                                     let uu____15724 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl in
                                     solve env uu____15724
                                   else
                                     (let uu____15726 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                      match uu____15726 with
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
                                          let uu____15758 =
                                            let uu____15765 =
                                              let uu____15768 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs in
                                              FStar_Syntax_Util.arrow zs
                                                uu____15768 in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____15765
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None in
                                          (match uu____15758 with
                                           | (uu____15771, w, wl1) ->
                                               let w_app =
                                                 let uu____15775 =
                                                   FStar_List.map
                                                     (fun uu____15786 ->
                                                        match uu____15786
                                                        with
                                                        | (z, uu____15794) ->
                                                            let uu____15799 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____15799) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____15775
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____15801 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____15801
                                                 then
                                                   let uu____15802 =
                                                     let uu____15805 =
                                                       flex_t_to_string lhs in
                                                     let uu____15806 =
                                                       let uu____15809 =
                                                         flex_t_to_string rhs in
                                                       let uu____15810 =
                                                         let uu____15813 =
                                                           term_to_string w in
                                                         let uu____15814 =
                                                           let uu____15817 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____15824 =
                                                             let uu____15827
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____15834
                                                               =
                                                               let uu____15837
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____15837] in
                                                             uu____15827 ::
                                                               uu____15834 in
                                                           uu____15817 ::
                                                             uu____15824 in
                                                         uu____15813 ::
                                                           uu____15814 in
                                                       uu____15809 ::
                                                         uu____15810 in
                                                     uu____15805 ::
                                                       uu____15806 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____15802
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____15843 =
                                                       let uu____15848 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____15848) in
                                                     TERM uu____15843 in
                                                   let uu____15849 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____15849
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____15854 =
                                                          let uu____15859 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____15859) in
                                                        TERM uu____15854 in
                                                      [s1; s2]) in
                                                 let uu____15860 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____15860))))))
                     | uu____15861 ->
                         let uu____15878 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____15878)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____15927 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____15927
            then
              let uu____15928 = FStar_Syntax_Print.term_to_string t1 in
              let uu____15929 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____15930 = FStar_Syntax_Print.term_to_string t2 in
              let uu____15931 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15928 uu____15929 uu____15930 uu____15931
            else ());
           (let uu____15934 = FStar_Syntax_Util.head_and_args t1 in
            match uu____15934 with
            | (head1, args1) ->
                let uu____15977 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____15977 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16042 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____16042 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____16046 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____16046) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16064 =
                         mklstr
                           (fun uu____16075 ->
                              let uu____16076 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____16077 = args_to_string args1 in
                              let uu____16080 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____16081 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____16076 uu____16077 uu____16080
                                uu____16081) in
                       giveup env1 uu____16064 orig
                     else
                       (let uu____16085 =
                          (nargs = Prims.int_zero) ||
                            (let uu____16087 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____16087 = FStar_Syntax_Util.Equal) in
                        if uu____16085
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2614_16089 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2614_16089.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2614_16089.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2614_16089.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2614_16089.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2614_16089.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2614_16089.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2614_16089.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2614_16089.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____16096 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____16096
                                    else solve env1 wl2))
                        else
                          (let uu____16099 = base_and_refinement env1 t1 in
                           match uu____16099 with
                           | (base1, refinement1) ->
                               let uu____16124 = base_and_refinement env1 t2 in
                               (match uu____16124 with
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
                                           let uu____16287 =
                                             FStar_List.fold_right
                                               (fun uu____16327 ->
                                                  fun uu____16328 ->
                                                    match (uu____16327,
                                                            uu____16328)
                                                    with
                                                    | (((a1, uu____16380),
                                                        (a2, uu____16382)),
                                                       (probs, wl3)) ->
                                                        let uu____16431 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____16431
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____16287 with
                                           | (subprobs, wl3) ->
                                               ((let uu____16473 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16473
                                                 then
                                                   let uu____16474 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____16474
                                                 else ());
                                                (let uu____16477 =
                                                   FStar_Options.defensive () in
                                                 if uu____16477
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
                                                    (let uu____16497 =
                                                       mk_sub_probs wl3 in
                                                     match uu____16497 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____16513 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____16513 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____16521 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____16521)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____16545 =
                                                    mk_sub_probs wl3 in
                                                  match uu____16545 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____16561 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____16561 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____16569 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____16569) in
                                         let unfold_and_retry d env2 wl2
                                           uu____16596 =
                                           match uu____16596 with
                                           | (prob, reason) ->
                                               ((let uu____16610 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16610
                                                 then
                                                   let uu____16611 =
                                                     prob_to_string env2 orig in
                                                   let uu____16612 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____16611 uu____16612
                                                 else ());
                                                (let uu____16614 =
                                                   let uu____16623 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____16626 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____16623, uu____16626) in
                                                 match uu____16614 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____16639 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____16639 with
                                                      | (head1', uu____16657)
                                                          ->
                                                          let uu____16682 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____16682
                                                           with
                                                           | (head2',
                                                              uu____16700) ->
                                                               let uu____16725
                                                                 =
                                                                 let uu____16730
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____16731
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____16730,
                                                                   uu____16731) in
                                                               (match uu____16725
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
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
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____16735
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____16736
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____16737
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____16734
                                                                    uu____16735
                                                                    uu____16736
                                                                    uu____16737
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____16739
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2702_16747
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2702_16747.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2702_16747.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2702_16747.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2702_16747.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2702_16747.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2702_16747.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2702_16747.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2702_16747.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
                                                                    let uu____16749
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____16749
                                                                    then
                                                                    let uu____16750
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____16750
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____16752 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____16764 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____16764 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____16771 =
                                             let uu____16772 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____16772.FStar_Syntax_Syntax.n in
                                           match uu____16771 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____16776 -> false in
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
                                          | uu____16778 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____16781 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2722_16817 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2722_16817.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2722_16817.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2722_16817.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2722_16817.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2722_16817.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2722_16817.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2722_16817.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2722_16817.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16892 = destruct_flex_t scrutinee wl1 in
             match uu____16892 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____16903 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____16903 with
                  | (xs, pat_term, uu____16918, uu____16919) ->
                      let uu____16924 =
                        FStar_List.fold_left
                          (fun uu____16947 ->
                             fun x ->
                               match uu____16947 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____16968 = copy_uvar uv [] t_x wl3 in
                                   (match uu____16968 with
                                    | (uu____16987, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____16924 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____17008 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____17008 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2763_17024 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2763_17024.wl_deferred_to_tac);
                                    ctr = (uu___2763_17024.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2763_17024.umax_heuristic_ok);
                                    tcenv = (uu___2763_17024.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2763_17024.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____17032 = solve env1 wl' in
                                (match uu____17032 with
                                 | Success (uu____17035, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2772_17039 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2772_17039.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2772_17039.wl_deferred_to_tac);
                                         ctr = (uu___2772_17039.ctr);
                                         defer_ok =
                                           (uu___2772_17039.defer_ok);
                                         smt_ok = (uu___2772_17039.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2772_17039.umax_heuristic_ok);
                                         tcenv = (uu___2772_17039.tcenv);
                                         wl_implicits =
                                           (uu___2772_17039.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2772_17039.repr_subcomp_allowed)
                                       } in
                                     let uu____17040 = solve env1 wl'1 in
                                     (match uu____17040 with
                                      | Success
                                          (uu____17043, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____17047 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____17047))
                                      | Failed uu____17052 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17058 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____17079 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____17079
                 then
                   let uu____17080 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____17081 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17080 uu____17081
                 else ());
                (let uu____17083 =
                   let uu____17104 =
                     let uu____17113 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____17113) in
                   let uu____17120 =
                     let uu____17129 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____17129) in
                   (uu____17104, uu____17120) in
                 match uu____17083 with
                 | ((uu____17158,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____17161;
                       FStar_Syntax_Syntax.vars = uu____17162;_}),
                    (s, t)) ->
                     let uu____17233 =
                       let uu____17234 = is_flex scrutinee in
                       Prims.op_Negation uu____17234 in
                     if uu____17233
                     then
                       ((let uu____17242 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____17242
                         then
                           let uu____17243 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17243
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17255 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17255
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17261 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17261
                           then
                             let uu____17262 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____17263 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17262 uu____17263
                           else ());
                          (let pat_discriminates uu___26_17284 =
                             match uu___26_17284 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17299;
                                  FStar_Syntax_Syntax.p = uu____17300;_},
                                FStar_Pervasives_Native.None, uu____17301) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17314;
                                  FStar_Syntax_Syntax.p = uu____17315;_},
                                FStar_Pervasives_Native.None, uu____17316) ->
                                 true
                             | uu____17341 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____17441 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____17441 with
                                       | (uu____17442, uu____17443, t') ->
                                           let uu____17461 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____17461 with
                                            | (FullMatch, uu____17472) ->
                                                true
                                            | (HeadMatch uu____17485,
                                               uu____17486) -> true
                                            | uu____17499 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____17532 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____17532
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17537 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____17537 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____17625, uu____17626)
                                       -> branches1
                                   | uu____17771 -> branches in
                                 let uu____17826 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____17835 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____17835 with
                                        | (p, uu____17839, uu____17840) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____17867 ->
                                      FStar_Util.Inr uu____17867) uu____17826))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17897 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____17897 with
                                | (p, uu____17905, e) ->
                                    ((let uu____17924 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____17924
                                      then
                                        let uu____17925 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____17926 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17925 uu____17926
                                      else ());
                                     (let uu____17928 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____17941 ->
                                           FStar_Util.Inr uu____17941)
                                        uu____17928)))))
                 | ((s, t),
                    (uu____17944,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____17947;
                       FStar_Syntax_Syntax.vars = uu____17948;_}))
                     ->
                     let uu____18017 =
                       let uu____18018 = is_flex scrutinee in
                       Prims.op_Negation uu____18018 in
                     if uu____18017
                     then
                       ((let uu____18026 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____18026
                         then
                           let uu____18027 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18027
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18039 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18039
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18045 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18045
                           then
                             let uu____18046 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____18047 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18046 uu____18047
                           else ());
                          (let pat_discriminates uu___26_18068 =
                             match uu___26_18068 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18083;
                                  FStar_Syntax_Syntax.p = uu____18084;_},
                                FStar_Pervasives_Native.None, uu____18085) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18098;
                                  FStar_Syntax_Syntax.p = uu____18099;_},
                                FStar_Pervasives_Native.None, uu____18100) ->
                                 true
                             | uu____18125 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____18225 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____18225 with
                                       | (uu____18226, uu____18227, t') ->
                                           let uu____18245 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____18245 with
                                            | (FullMatch, uu____18256) ->
                                                true
                                            | (HeadMatch uu____18269,
                                               uu____18270) -> true
                                            | uu____18283 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____18316 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____18316
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18321 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____18321 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____18409, uu____18410)
                                       -> branches1
                                   | uu____18555 -> branches in
                                 let uu____18610 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____18619 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____18619 with
                                        | (p, uu____18623, uu____18624) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____18651 ->
                                      FStar_Util.Inr uu____18651) uu____18610))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18681 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____18681 with
                                | (p, uu____18689, e) ->
                                    ((let uu____18708 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____18708
                                      then
                                        let uu____18709 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____18710 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18709 uu____18710
                                      else ());
                                     (let uu____18712 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____18725 ->
                                           FStar_Util.Inr uu____18725)
                                        uu____18712)))))
                 | uu____18726 ->
                     ((let uu____18748 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____18748
                       then
                         let uu____18749 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____18750 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____18749 uu____18750
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____18792 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____18792
            then
              let uu____18793 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____18794 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____18795 = FStar_Syntax_Print.term_to_string t1 in
              let uu____18796 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____18793 uu____18794 uu____18795 uu____18796
            else ());
           (let uu____18798 = head_matches_delta env1 wl1 t1 t2 in
            match uu____18798 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____18829, uu____18830) ->
                     let rec may_relate head =
                       let uu____18857 =
                         let uu____18858 = FStar_Syntax_Subst.compress head in
                         uu____18858.FStar_Syntax_Syntax.n in
                       match uu____18857 with
                       | FStar_Syntax_Syntax.Tm_name uu____18861 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18862 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____18886 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____18886 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____18887 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____18888
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____18889 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____18891, uu____18892) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____18934) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____18940) ->
                           may_relate t
                       | uu____18945 -> false in
                     let uu____18946 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____18946 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____18956 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____18956
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____18962 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____18962
                          then
                            let uu____18963 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____18963 with
                             | (guard, wl2) ->
                                 let uu____18970 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____18970)
                          else
                            (let uu____18972 =
                               mklstr
                                 (fun uu____18983 ->
                                    let uu____18984 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____18985 =
                                      let uu____18986 =
                                        let uu____18989 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____18989
                                          (fun x ->
                                             let uu____18995 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____18995) in
                                      FStar_Util.dflt "" uu____18986 in
                                    let uu____18996 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____18997 =
                                      let uu____18998 =
                                        let uu____19001 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____19001
                                          (fun x ->
                                             let uu____19007 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____19007) in
                                      FStar_Util.dflt "" uu____18998 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____18984 uu____18985 uu____18996
                                      uu____18997) in
                             giveup env1 uu____18972 orig))
                 | (HeadMatch (true), uu____19008) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____19021 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____19021 with
                        | (guard, wl2) ->
                            let uu____19028 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____19028)
                     else
                       (let uu____19030 =
                          mklstr
                            (fun uu____19037 ->
                               let uu____19038 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____19039 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____19038 uu____19039) in
                        giveup env1 uu____19030 orig)
                 | (uu____19040, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2954_19054 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2954_19054.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2954_19054.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2954_19054.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2954_19054.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2954_19054.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2954_19054.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2954_19054.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2954_19054.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____19078 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____19078
          then
            let uu____19079 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____19079
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____19084 =
                let uu____19087 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19087 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____19084 t1);
             (let uu____19105 =
                let uu____19108 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19108 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____19105 t2);
             (let uu____19126 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____19126
              then
                let uu____19127 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____19128 =
                  let uu____19129 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____19130 =
                    let uu____19131 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____19131 in
                  Prims.op_Hat uu____19129 uu____19130 in
                let uu____19132 =
                  let uu____19133 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____19134 =
                    let uu____19135 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____19135 in
                  Prims.op_Hat uu____19133 uu____19134 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____19127 uu____19128 uu____19132
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____19138, uu____19139) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____19154, FStar_Syntax_Syntax.Tm_delayed uu____19155) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____19170, uu____19171) ->
                  let uu____19198 =
                    let uu___2985_19199 = problem in
                    let uu____19200 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2985_19199.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19200;
                      FStar_TypeChecker_Common.relation =
                        (uu___2985_19199.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2985_19199.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2985_19199.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2985_19199.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2985_19199.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2985_19199.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2985_19199.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2985_19199.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19198 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____19201, uu____19202) ->
                  let uu____19209 =
                    let uu___2991_19210 = problem in
                    let uu____19211 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2991_19210.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19211;
                      FStar_TypeChecker_Common.relation =
                        (uu___2991_19210.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2991_19210.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2991_19210.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2991_19210.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2991_19210.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2991_19210.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2991_19210.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2991_19210.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19209 wl
              | (uu____19212, FStar_Syntax_Syntax.Tm_ascribed uu____19213) ->
                  let uu____19240 =
                    let uu___2997_19241 = problem in
                    let uu____19242 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2997_19241.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2997_19241.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2997_19241.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19242;
                      FStar_TypeChecker_Common.element =
                        (uu___2997_19241.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2997_19241.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2997_19241.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2997_19241.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2997_19241.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2997_19241.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19240 wl
              | (uu____19243, FStar_Syntax_Syntax.Tm_meta uu____19244) ->
                  let uu____19251 =
                    let uu___3003_19252 = problem in
                    let uu____19253 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3003_19252.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3003_19252.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3003_19252.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19253;
                      FStar_TypeChecker_Common.element =
                        (uu___3003_19252.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3003_19252.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3003_19252.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3003_19252.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3003_19252.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3003_19252.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19251 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____19255),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____19257)) ->
                  let uu____19266 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____19266
              | (FStar_Syntax_Syntax.Tm_bvar uu____19267, uu____19268) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____19269, FStar_Syntax_Syntax.Tm_bvar uu____19270) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_19339 =
                    match uu___27_19339 with
                    | [] -> c
                    | bs ->
                        let uu____19367 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____19367 in
                  let uu____19378 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____19378 with
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
                                    let uu____19527 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____19527
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_19612 =
                    match uu___28_19612 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____19654 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____19654 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____19799 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____19800 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____19799
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____19800 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____19801, uu____19802) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19831 -> true
                    | uu____19850 -> false in
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
                      (let uu____19903 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3105_19911 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3105_19911.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3105_19911.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3105_19911.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3105_19911.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3105_19911.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3105_19911.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3105_19911.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3105_19911.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3105_19911.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3105_19911.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3105_19911.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3105_19911.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3105_19911.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3105_19911.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3105_19911.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3105_19911.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3105_19911.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3105_19911.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3105_19911.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3105_19911.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3105_19911.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3105_19911.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3105_19911.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3105_19911.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3105_19911.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3105_19911.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3105_19911.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3105_19911.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3105_19911.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3105_19911.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3105_19911.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3105_19911.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3105_19911.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3105_19911.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3105_19911.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3105_19911.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3105_19911.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3105_19911.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3105_19911.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3105_19911.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3105_19911.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3105_19911.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3105_19911.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3105_19911.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____19903 with
                       | (uu____19914, ty, uu____19916) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____19925 =
                                 let uu____19926 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____19926.FStar_Syntax_Syntax.n in
                               match uu____19925 with
                               | FStar_Syntax_Syntax.Tm_refine uu____19929 ->
                                   let uu____19936 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____19936
                               | uu____19937 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____19940 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____19940
                             then
                               let uu____19941 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____19942 =
                                 let uu____19943 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____19943 in
                               let uu____19944 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____19941 uu____19942 uu____19944
                             else ());
                            r1)) in
                  let uu____19946 =
                    let uu____19963 = maybe_eta t1 in
                    let uu____19970 = maybe_eta t2 in
                    (uu____19963, uu____19970) in
                  (match uu____19946 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3126_20012 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3126_20012.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3126_20012.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3126_20012.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3126_20012.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3126_20012.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3126_20012.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3126_20012.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3126_20012.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20033 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20033
                       then
                         let uu____20034 = destruct_flex_t not_abs wl in
                         (match uu____20034 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3143_20049 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3143_20049.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3143_20049.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3143_20049.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3143_20049.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3143_20049.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3143_20049.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3143_20049.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3143_20049.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20051 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20051 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20072 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20072
                       then
                         let uu____20073 = destruct_flex_t not_abs wl in
                         (match uu____20073 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3143_20088 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3143_20088.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3143_20088.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3143_20088.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3143_20088.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3143_20088.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3143_20088.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3143_20088.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3143_20088.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20090 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20090 orig))
                   | uu____20091 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____20108, FStar_Syntax_Syntax.Tm_abs uu____20109) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20138 -> true
                    | uu____20157 -> false in
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
                      (let uu____20210 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3105_20218 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3105_20218.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3105_20218.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3105_20218.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3105_20218.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3105_20218.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3105_20218.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3105_20218.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3105_20218.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3105_20218.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3105_20218.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3105_20218.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3105_20218.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3105_20218.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3105_20218.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3105_20218.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3105_20218.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3105_20218.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3105_20218.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3105_20218.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3105_20218.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3105_20218.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3105_20218.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3105_20218.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3105_20218.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3105_20218.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3105_20218.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3105_20218.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3105_20218.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3105_20218.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3105_20218.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3105_20218.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3105_20218.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3105_20218.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3105_20218.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3105_20218.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3105_20218.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3105_20218.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3105_20218.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3105_20218.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3105_20218.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3105_20218.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3105_20218.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3105_20218.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3105_20218.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____20210 with
                       | (uu____20221, ty, uu____20223) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____20232 =
                                 let uu____20233 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____20233.FStar_Syntax_Syntax.n in
                               match uu____20232 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20236 ->
                                   let uu____20243 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____20243
                               | uu____20244 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____20247 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____20247
                             then
                               let uu____20248 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____20249 =
                                 let uu____20250 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20250 in
                               let uu____20251 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20248 uu____20249 uu____20251
                             else ());
                            r1)) in
                  let uu____20253 =
                    let uu____20270 = maybe_eta t1 in
                    let uu____20277 = maybe_eta t2 in
                    (uu____20270, uu____20277) in
                  (match uu____20253 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3126_20319 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3126_20319.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3126_20319.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3126_20319.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3126_20319.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3126_20319.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3126_20319.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3126_20319.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3126_20319.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20340 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20340
                       then
                         let uu____20341 = destruct_flex_t not_abs wl in
                         (match uu____20341 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3143_20356 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3143_20356.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3143_20356.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3143_20356.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3143_20356.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3143_20356.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3143_20356.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3143_20356.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3143_20356.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20358 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20358 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20379 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20379
                       then
                         let uu____20380 = destruct_flex_t not_abs wl in
                         (match uu____20380 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3143_20395 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3143_20395.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3143_20395.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3143_20395.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3143_20395.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3143_20395.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3143_20395.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3143_20395.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3143_20395.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20397 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20397 orig))
                   | uu____20398 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____20427 =
                    let uu____20432 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____20432 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3166_20460 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3166_20460.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3166_20460.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3168_20462 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3168_20462.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3168_20462.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____20463, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3166_20477 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3166_20477.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3166_20477.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3168_20479 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3168_20479.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3168_20479.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____20480 -> (x1, x2) in
                  (match uu____20427 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____20499 = as_refinement false env t11 in
                       (match uu____20499 with
                        | (x12, phi11) ->
                            let uu____20506 = as_refinement false env t21 in
                            (match uu____20506 with
                             | (x22, phi21) ->
                                 ((let uu____20514 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____20514
                                   then
                                     ((let uu____20516 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____20517 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____20518 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____20516
                                         uu____20517 uu____20518);
                                      (let uu____20519 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____20520 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____20521 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____20519
                                         uu____20520 uu____20521))
                                   else ());
                                  (let uu____20523 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____20523 with
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
                                         let uu____20591 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____20591
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____20603 =
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
                                         (let uu____20614 =
                                            let uu____20617 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20617 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____20614
                                            (p_guard base_prob));
                                         (let uu____20635 =
                                            let uu____20638 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20638 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____20635
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____20656 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____20656) in
                                       let has_uvars =
                                         (let uu____20660 =
                                            let uu____20661 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____20661 in
                                          Prims.op_Negation uu____20660) ||
                                           (let uu____20665 =
                                              let uu____20666 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____20666 in
                                            Prims.op_Negation uu____20665) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____20669 =
                                           let uu____20674 =
                                             let uu____20683 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____20683] in
                                           mk_t_problem wl1 uu____20674 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____20669 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____20705 =
                                                solve env1
                                                  (let uu___3211_20707 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3211_20707.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3211_20707.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3211_20707.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3211_20707.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3211_20707.tcenv);
                                                     wl_implicits =
                                                       (uu___3211_20707.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3211_20707.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____20705 with
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
                                                   (uu____20718,
                                                    defer_to_tac,
                                                    uu____20720)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____20725 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____20725 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3227_20734 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3227_20734.attempting);
                                                         wl_deferred =
                                                           (uu___3227_20734.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3227_20734.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3227_20734.defer_ok);
                                                         smt_ok =
                                                           (uu___3227_20734.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3227_20734.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3227_20734.tcenv);
                                                         wl_implicits =
                                                           (uu___3227_20734.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3227_20734.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____20736 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____20736))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20738,
                 FStar_Syntax_Syntax.Tm_uvar uu____20739) ->
                  let uu____20764 = ensure_no_uvar_subst t1 wl in
                  (match uu____20764 with
                   | (t11, wl1) ->
                       let uu____20771 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20771 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20780;
                    FStar_Syntax_Syntax.pos = uu____20781;
                    FStar_Syntax_Syntax.vars = uu____20782;_},
                  uu____20783),
                 FStar_Syntax_Syntax.Tm_uvar uu____20784) ->
                  let uu____20833 = ensure_no_uvar_subst t1 wl in
                  (match uu____20833 with
                   | (t11, wl1) ->
                       let uu____20840 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20840 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20849,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20850;
                    FStar_Syntax_Syntax.pos = uu____20851;
                    FStar_Syntax_Syntax.vars = uu____20852;_},
                  uu____20853)) ->
                  let uu____20902 = ensure_no_uvar_subst t1 wl in
                  (match uu____20902 with
                   | (t11, wl1) ->
                       let uu____20909 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20909 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20918;
                    FStar_Syntax_Syntax.pos = uu____20919;
                    FStar_Syntax_Syntax.vars = uu____20920;_},
                  uu____20921),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20922;
                    FStar_Syntax_Syntax.pos = uu____20923;
                    FStar_Syntax_Syntax.vars = uu____20924;_},
                  uu____20925)) ->
                  let uu____20998 = ensure_no_uvar_subst t1 wl in
                  (match uu____20998 with
                   | (t11, wl1) ->
                       let uu____21005 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21005 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____21014, uu____21015) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21028 = destruct_flex_t t1 wl in
                  (match uu____21028 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21035;
                    FStar_Syntax_Syntax.pos = uu____21036;
                    FStar_Syntax_Syntax.vars = uu____21037;_},
                  uu____21038),
                 uu____21039) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21076 = destruct_flex_t t1 wl in
                  (match uu____21076 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____21083, FStar_Syntax_Syntax.Tm_uvar uu____21084) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____21097, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21098;
                    FStar_Syntax_Syntax.pos = uu____21099;
                    FStar_Syntax_Syntax.vars = uu____21100;_},
                  uu____21101)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____21138,
                 FStar_Syntax_Syntax.Tm_arrow uu____21139) ->
                  solve_t' env
                    (let uu___3330_21167 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3330_21167.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3330_21167.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3330_21167.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3330_21167.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3330_21167.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3330_21167.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3330_21167.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3330_21167.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3330_21167.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21168;
                    FStar_Syntax_Syntax.pos = uu____21169;
                    FStar_Syntax_Syntax.vars = uu____21170;_},
                  uu____21171),
                 FStar_Syntax_Syntax.Tm_arrow uu____21172) ->
                  solve_t' env
                    (let uu___3330_21224 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3330_21224.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3330_21224.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3330_21224.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3330_21224.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3330_21224.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3330_21224.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3330_21224.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3330_21224.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3330_21224.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21225, FStar_Syntax_Syntax.Tm_uvar uu____21226) ->
                  let uu____21239 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21239
              | (uu____21240, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21241;
                    FStar_Syntax_Syntax.pos = uu____21242;
                    FStar_Syntax_Syntax.vars = uu____21243;_},
                  uu____21244)) ->
                  let uu____21281 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21281
              | (FStar_Syntax_Syntax.Tm_uvar uu____21282, uu____21283) ->
                  let uu____21296 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21296
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21297;
                    FStar_Syntax_Syntax.pos = uu____21298;
                    FStar_Syntax_Syntax.vars = uu____21299;_},
                  uu____21300),
                 uu____21301) ->
                  let uu____21338 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21338
              | (FStar_Syntax_Syntax.Tm_refine uu____21339, uu____21340) ->
                  let t21 =
                    let uu____21348 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____21348 in
                  solve_t env
                    (let uu___3365_21374 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3365_21374.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3365_21374.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3365_21374.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3365_21374.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3365_21374.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3365_21374.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3365_21374.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3365_21374.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3365_21374.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21375, FStar_Syntax_Syntax.Tm_refine uu____21376) ->
                  let t11 =
                    let uu____21384 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____21384 in
                  solve_t env
                    (let uu___3372_21410 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3372_21410.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3372_21410.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3372_21410.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3372_21410.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3372_21410.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3372_21410.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3372_21410.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3372_21410.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3372_21410.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____21492 =
                    let uu____21493 = guard_of_prob env wl problem t1 t2 in
                    match uu____21493 with
                    | (guard, wl1) ->
                        let uu____21500 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____21500 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____21719 = br1 in
                        (match uu____21719 with
                         | (p1, w1, uu____21748) ->
                             let uu____21765 = br2 in
                             (match uu____21765 with
                              | (p2, w2, uu____21788) ->
                                  let uu____21793 =
                                    let uu____21794 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____21794 in
                                  if uu____21793
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____21818 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____21818 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____21855 = br2 in
                                         (match uu____21855 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____21888 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____21888 in
                                              let uu____21893 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____21924,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____21945) ->
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
                                                    let uu____22004 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____22004 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____21893
                                                (fun uu____22075 ->
                                                   match uu____22075 with
                                                   | (wprobs, wl2) ->
                                                       let uu____22112 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____22112
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____22132
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____22132
                                                              then
                                                                let uu____22133
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____22134
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____22133
                                                                  uu____22134
                                                              else ());
                                                             (let uu____22136
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____22136
                                                                (fun
                                                                   uu____22172
                                                                   ->
                                                                   match uu____22172
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
                    | uu____22301 -> FStar_Pervasives_Native.None in
                  let uu____22342 = solve_branches wl brs1 brs2 in
                  (match uu____22342 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____22366 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____22366 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____22391 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____22391 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____22424 =
                                FStar_List.map
                                  (fun uu____22436 ->
                                     match uu____22436 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____22424 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____22445 =
                              let uu____22446 =
                                let uu____22447 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____22447
                                  (let uu___3471_22455 = wl3 in
                                   {
                                     attempting =
                                       (uu___3471_22455.attempting);
                                     wl_deferred =
                                       (uu___3471_22455.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3471_22455.wl_deferred_to_tac);
                                     ctr = (uu___3471_22455.ctr);
                                     defer_ok = (uu___3471_22455.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3471_22455.umax_heuristic_ok);
                                     tcenv = (uu___3471_22455.tcenv);
                                     wl_implicits =
                                       (uu___3471_22455.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3471_22455.repr_subcomp_allowed)
                                   }) in
                              solve env uu____22446 in
                            (match uu____22445 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____22460 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____22467 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____22467 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____22468, uu____22469) ->
                  let head1 =
                    let uu____22493 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22493
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22539 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22539
                      FStar_Pervasives_Native.fst in
                  ((let uu____22585 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22585
                    then
                      let uu____22586 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22587 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22588 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22586 uu____22587 uu____22588
                    else ());
                   (let no_free_uvars t =
                      (let uu____22598 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22598) &&
                        (let uu____22602 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22602) in
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
                      let uu____22618 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22618 = FStar_Syntax_Util.Equal in
                    let uu____22619 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22619
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22620 = equal t1 t2 in
                         (if uu____22620
                          then
                            let uu____22621 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22621
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22624 =
                            let uu____22631 = equal t1 t2 in
                            if uu____22631
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22641 = mk_eq2 wl env orig t1 t2 in
                               match uu____22641 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22624 with
                          | (guard, wl1) ->
                              let uu____22662 = solve_prob orig guard [] wl1 in
                              solve env uu____22662))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____22664, uu____22665) ->
                  let head1 =
                    let uu____22673 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22673
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22719 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22719
                      FStar_Pervasives_Native.fst in
                  ((let uu____22765 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22765
                    then
                      let uu____22766 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22767 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22768 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22766 uu____22767 uu____22768
                    else ());
                   (let no_free_uvars t =
                      (let uu____22778 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22778) &&
                        (let uu____22782 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22782) in
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
                      let uu____22798 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22798 = FStar_Syntax_Util.Equal in
                    let uu____22799 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22799
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22800 = equal t1 t2 in
                         (if uu____22800
                          then
                            let uu____22801 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22801
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22804 =
                            let uu____22811 = equal t1 t2 in
                            if uu____22811
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22821 = mk_eq2 wl env orig t1 t2 in
                               match uu____22821 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22804 with
                          | (guard, wl1) ->
                              let uu____22842 = solve_prob orig guard [] wl1 in
                              solve env uu____22842))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____22844, uu____22845) ->
                  let head1 =
                    let uu____22847 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22847
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22893 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22893
                      FStar_Pervasives_Native.fst in
                  ((let uu____22939 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22939
                    then
                      let uu____22940 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22941 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22942 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22940 uu____22941 uu____22942
                    else ());
                   (let no_free_uvars t =
                      (let uu____22952 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22952) &&
                        (let uu____22956 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22956) in
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
                      let uu____22972 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22972 = FStar_Syntax_Util.Equal in
                    let uu____22973 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22973
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22974 = equal t1 t2 in
                         (if uu____22974
                          then
                            let uu____22975 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22975
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22978 =
                            let uu____22985 = equal t1 t2 in
                            if uu____22985
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22995 = mk_eq2 wl env orig t1 t2 in
                               match uu____22995 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22978 with
                          | (guard, wl1) ->
                              let uu____23016 = solve_prob orig guard [] wl1 in
                              solve env uu____23016))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____23018, uu____23019) ->
                  let head1 =
                    let uu____23021 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23021
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23067 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23067
                      FStar_Pervasives_Native.fst in
                  ((let uu____23113 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23113
                    then
                      let uu____23114 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23115 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23116 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23114 uu____23115 uu____23116
                    else ());
                   (let no_free_uvars t =
                      (let uu____23126 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23126) &&
                        (let uu____23130 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23130) in
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
                      let uu____23146 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23146 = FStar_Syntax_Util.Equal in
                    let uu____23147 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23147
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23148 = equal t1 t2 in
                         (if uu____23148
                          then
                            let uu____23149 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23149
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23152 =
                            let uu____23159 = equal t1 t2 in
                            if uu____23159
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23169 = mk_eq2 wl env orig t1 t2 in
                               match uu____23169 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23152 with
                          | (guard, wl1) ->
                              let uu____23190 = solve_prob orig guard [] wl1 in
                              solve env uu____23190))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____23192, uu____23193) ->
                  let head1 =
                    let uu____23195 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23195
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23235 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23235
                      FStar_Pervasives_Native.fst in
                  ((let uu____23275 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23275
                    then
                      let uu____23276 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23277 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23278 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23276 uu____23277 uu____23278
                    else ());
                   (let no_free_uvars t =
                      (let uu____23288 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23288) &&
                        (let uu____23292 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23292) in
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
                      let uu____23308 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23308 = FStar_Syntax_Util.Equal in
                    let uu____23309 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23309
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23310 = equal t1 t2 in
                         (if uu____23310
                          then
                            let uu____23311 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23311
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23314 =
                            let uu____23321 = equal t1 t2 in
                            if uu____23321
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23331 = mk_eq2 wl env orig t1 t2 in
                               match uu____23331 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23314 with
                          | (guard, wl1) ->
                              let uu____23352 = solve_prob orig guard [] wl1 in
                              solve env uu____23352))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____23354, uu____23355) ->
                  let head1 =
                    let uu____23373 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23373
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23413 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23413
                      FStar_Pervasives_Native.fst in
                  ((let uu____23453 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23453
                    then
                      let uu____23454 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23455 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23456 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23454 uu____23455 uu____23456
                    else ());
                   (let no_free_uvars t =
                      (let uu____23466 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23466) &&
                        (let uu____23470 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23470) in
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
                      let uu____23486 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23486 = FStar_Syntax_Util.Equal in
                    let uu____23487 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23487
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23488 = equal t1 t2 in
                         (if uu____23488
                          then
                            let uu____23489 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23489
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23492 =
                            let uu____23499 = equal t1 t2 in
                            if uu____23499
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23509 = mk_eq2 wl env orig t1 t2 in
                               match uu____23509 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23492 with
                          | (guard, wl1) ->
                              let uu____23530 = solve_prob orig guard [] wl1 in
                              solve env uu____23530))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23532, FStar_Syntax_Syntax.Tm_match uu____23533) ->
                  let head1 =
                    let uu____23557 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23557
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23597 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23597
                      FStar_Pervasives_Native.fst in
                  ((let uu____23637 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23637
                    then
                      let uu____23638 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23639 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23640 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23638 uu____23639 uu____23640
                    else ());
                   (let no_free_uvars t =
                      (let uu____23650 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23650) &&
                        (let uu____23654 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23654) in
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
                      let uu____23670 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23670 = FStar_Syntax_Util.Equal in
                    let uu____23671 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23671
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23672 = equal t1 t2 in
                         (if uu____23672
                          then
                            let uu____23673 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23673
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23676 =
                            let uu____23683 = equal t1 t2 in
                            if uu____23683
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23693 = mk_eq2 wl env orig t1 t2 in
                               match uu____23693 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23676 with
                          | (guard, wl1) ->
                              let uu____23714 = solve_prob orig guard [] wl1 in
                              solve env uu____23714))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23716, FStar_Syntax_Syntax.Tm_uinst uu____23717) ->
                  let head1 =
                    let uu____23725 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23725
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23765 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23765
                      FStar_Pervasives_Native.fst in
                  ((let uu____23805 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23805
                    then
                      let uu____23806 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23807 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23808 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23806 uu____23807 uu____23808
                    else ());
                   (let no_free_uvars t =
                      (let uu____23818 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23818) &&
                        (let uu____23822 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23822) in
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
                      let uu____23838 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23838 = FStar_Syntax_Util.Equal in
                    let uu____23839 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23839
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23840 = equal t1 t2 in
                         (if uu____23840
                          then
                            let uu____23841 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23841
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23844 =
                            let uu____23851 = equal t1 t2 in
                            if uu____23851
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23861 = mk_eq2 wl env orig t1 t2 in
                               match uu____23861 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23844 with
                          | (guard, wl1) ->
                              let uu____23882 = solve_prob orig guard [] wl1 in
                              solve env uu____23882))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23884, FStar_Syntax_Syntax.Tm_name uu____23885) ->
                  let head1 =
                    let uu____23887 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23887
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23927 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23927
                      FStar_Pervasives_Native.fst in
                  ((let uu____23967 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23967
                    then
                      let uu____23968 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23969 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23970 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23968 uu____23969 uu____23970
                    else ());
                   (let no_free_uvars t =
                      (let uu____23980 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23980) &&
                        (let uu____23984 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23984) in
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
                      let uu____24000 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24000 = FStar_Syntax_Util.Equal in
                    let uu____24001 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24001
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24002 = equal t1 t2 in
                         (if uu____24002
                          then
                            let uu____24003 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24003
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24006 =
                            let uu____24013 = equal t1 t2 in
                            if uu____24013
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24023 = mk_eq2 wl env orig t1 t2 in
                               match uu____24023 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24006 with
                          | (guard, wl1) ->
                              let uu____24044 = solve_prob orig guard [] wl1 in
                              solve env uu____24044))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24046, FStar_Syntax_Syntax.Tm_constant uu____24047) ->
                  let head1 =
                    let uu____24049 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24049
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24089 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24089
                      FStar_Pervasives_Native.fst in
                  ((let uu____24129 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24129
                    then
                      let uu____24130 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24131 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24132 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24130 uu____24131 uu____24132
                    else ());
                   (let no_free_uvars t =
                      (let uu____24142 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24142) &&
                        (let uu____24146 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24146) in
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
                      let uu____24162 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24162 = FStar_Syntax_Util.Equal in
                    let uu____24163 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24163
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24164 = equal t1 t2 in
                         (if uu____24164
                          then
                            let uu____24165 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24165
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24168 =
                            let uu____24175 = equal t1 t2 in
                            if uu____24175
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24185 = mk_eq2 wl env orig t1 t2 in
                               match uu____24185 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24168 with
                          | (guard, wl1) ->
                              let uu____24206 = solve_prob orig guard [] wl1 in
                              solve env uu____24206))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24208, FStar_Syntax_Syntax.Tm_fvar uu____24209) ->
                  let head1 =
                    let uu____24211 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24211
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24257 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24257
                      FStar_Pervasives_Native.fst in
                  ((let uu____24303 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24303
                    then
                      let uu____24304 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24305 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24306 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24304 uu____24305 uu____24306
                    else ());
                   (let no_free_uvars t =
                      (let uu____24316 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24316) &&
                        (let uu____24320 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24320) in
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
                      let uu____24336 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24336 = FStar_Syntax_Util.Equal in
                    let uu____24337 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24337
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24338 = equal t1 t2 in
                         (if uu____24338
                          then
                            let uu____24339 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24339
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24342 =
                            let uu____24349 = equal t1 t2 in
                            if uu____24349
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24359 = mk_eq2 wl env orig t1 t2 in
                               match uu____24359 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24342 with
                          | (guard, wl1) ->
                              let uu____24380 = solve_prob orig guard [] wl1 in
                              solve env uu____24380))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24382, FStar_Syntax_Syntax.Tm_app uu____24383) ->
                  let head1 =
                    let uu____24401 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24401
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24441 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24441
                      FStar_Pervasives_Native.fst in
                  ((let uu____24481 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24481
                    then
                      let uu____24482 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24483 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24484 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24482 uu____24483 uu____24484
                    else ());
                   (let no_free_uvars t =
                      (let uu____24494 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24494) &&
                        (let uu____24498 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24498) in
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
                      let uu____24514 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24514 = FStar_Syntax_Util.Equal in
                    let uu____24515 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24515
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24516 = equal t1 t2 in
                         (if uu____24516
                          then
                            let uu____24517 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24517
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24520 =
                            let uu____24527 = equal t1 t2 in
                            if uu____24527
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24537 = mk_eq2 wl env orig t1 t2 in
                               match uu____24537 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24520 with
                          | (guard, wl1) ->
                              let uu____24558 = solve_prob orig guard [] wl1 in
                              solve env uu____24558))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____24560,
                 FStar_Syntax_Syntax.Tm_let uu____24561) ->
                  let uu____24586 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____24586
                  then
                    let uu____24587 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____24587
                  else
                    (let uu____24589 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____24589 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____24590, uu____24591) ->
                  let uu____24604 =
                    let uu____24609 =
                      let uu____24610 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24611 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24612 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24613 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24610 uu____24611 uu____24612 uu____24613 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24609) in
                  FStar_Errors.raise_error uu____24604
                    t1.FStar_Syntax_Syntax.pos
              | (uu____24614, FStar_Syntax_Syntax.Tm_let uu____24615) ->
                  let uu____24628 =
                    let uu____24633 =
                      let uu____24634 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24635 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24636 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24637 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24634 uu____24635 uu____24636 uu____24637 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24633) in
                  FStar_Errors.raise_error uu____24628
                    t1.FStar_Syntax_Syntax.pos
              | uu____24638 ->
                  let uu____24643 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____24643 orig))))
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
          (let uu____24705 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____24705
           then
             let uu____24706 =
               let uu____24707 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____24707 in
             let uu____24708 =
               let uu____24709 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____24709 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____24706 uu____24708
           else ());
          (let uu____24711 =
             let uu____24712 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____24712 in
           if uu____24711
           then
             let uu____24713 =
               mklstr
                 (fun uu____24720 ->
                    let uu____24721 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____24722 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____24721 uu____24722) in
             giveup env uu____24713 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____24740 =
                  mklstr
                    (fun uu____24747 ->
                       let uu____24748 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____24749 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____24748 uu____24749) in
                giveup env uu____24740 orig)
             else
               (let uu____24751 =
                  FStar_List.fold_left2
                    (fun uu____24772 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____24772 with
                           | (univ_sub_probs, wl1) ->
                               let uu____24793 =
                                 let uu____24798 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____24799 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____24798
                                   FStar_TypeChecker_Common.EQ uu____24799
                                   "effect universes" in
                               (match uu____24793 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____24751 with
                | (univ_sub_probs, wl1) ->
                    let uu____24818 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____24818 with
                     | (ret_sub_prob, wl2) ->
                         let uu____24825 =
                           FStar_List.fold_right2
                             (fun uu____24862 ->
                                fun uu____24863 ->
                                  fun uu____24864 ->
                                    match (uu____24862, uu____24863,
                                            uu____24864)
                                    with
                                    | ((a1, uu____24908), (a2, uu____24910),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____24943 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____24943 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____24825 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____24969 =
                                  let uu____24972 =
                                    let uu____24975 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____24975 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____24972 in
                                FStar_List.append univ_sub_probs uu____24969 in
                              let guard =
                                let guard =
                                  let uu____24994 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____24994 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3624_25003 = wl3 in
                                {
                                  attempting = (uu___3624_25003.attempting);
                                  wl_deferred = (uu___3624_25003.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3624_25003.wl_deferred_to_tac);
                                  ctr = (uu___3624_25003.ctr);
                                  defer_ok = (uu___3624_25003.defer_ok);
                                  smt_ok = (uu___3624_25003.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3624_25003.umax_heuristic_ok);
                                  tcenv = (uu___3624_25003.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3624_25003.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____25005 = attempt sub_probs wl5 in
                              solve env uu____25005)))) in
        let solve_layered_sub c11 c21 =
          (let uu____25018 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____25018
           then
             let uu____25019 =
               let uu____25020 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25020
                 FStar_Syntax_Print.comp_to_string in
             let uu____25021 =
               let uu____25022 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25022
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____25019 uu____25021
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____25027 =
                 let uu____25028 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25028 FStar_Ident.string_of_id in
               let uu____25029 =
                 let uu____25030 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25030 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____25027 uu____25029 in
             let lift_c1 edge =
               let uu____25045 =
                 let uu____25050 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____25050
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____25045
                 (fun uu____25067 ->
                    match uu____25067 with
                    | (c, g) ->
                        let uu____25078 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____25078, g)) in
             let uu____25079 =
               let uu____25090 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____25090 with
               | FStar_Pervasives_Native.None ->
                   let uu____25103 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____25103 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____25119 = lift_c1 edge in
                        (match uu____25119 with
                         | (c12, g_lift) ->
                             let uu____25136 =
                               let uu____25139 =
                                 let uu____25140 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____25140
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____25139
                                 (fun ts ->
                                    let uu____25146 =
                                      let uu____25147 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____25147
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____25146
                                      (fun uu____25158 ->
                                         FStar_Pervasives_Native.Some
                                           uu____25158)) in
                             (c12, g_lift, uu____25136, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____25162 =
                     let uu____25165 =
                       let uu____25166 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____25166
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____25165
                       (fun uu____25177 ->
                          FStar_Pervasives_Native.Some uu____25177) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____25162,
                     true) in
             match uu____25079 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____25188 =
                     mklstr
                       (fun uu____25195 ->
                          let uu____25196 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____25197 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____25196 uu____25197) in
                   giveup env uu____25188 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3659_25203 = wl in
                      {
                        attempting = (uu___3659_25203.attempting);
                        wl_deferred = (uu___3659_25203.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3659_25203.wl_deferred_to_tac);
                        ctr = (uu___3659_25203.ctr);
                        defer_ok = (uu___3659_25203.defer_ok);
                        smt_ok = (uu___3659_25203.smt_ok);
                        umax_heuristic_ok =
                          (uu___3659_25203.umax_heuristic_ok);
                        tcenv = (uu___3659_25203.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3659_25203.repr_subcomp_allowed)
                      } in
                    let uu____25204 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____25226 =
                             let uu____25227 = FStar_Syntax_Subst.compress t in
                             uu____25227.FStar_Syntax_Syntax.n in
                           match uu____25226 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____25230 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____25244)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____25250) ->
                               is_uvar t1
                           | uu____25275 -> false in
                         FStar_List.fold_right2
                           (fun uu____25308 ->
                              fun uu____25309 ->
                                fun uu____25310 ->
                                  match (uu____25308, uu____25309,
                                          uu____25310)
                                  with
                                  | ((a1, uu____25354), (a2, uu____25356),
                                     (is_sub_probs, wl2)) ->
                                      let uu____25389 = is_uvar a1 in
                                      if uu____25389
                                      then
                                        ((let uu____25397 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____25397
                                          then
                                            let uu____25398 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____25399 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____25398 uu____25399
                                          else ());
                                         (let uu____25401 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____25401 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____25204 with
                    | (is_sub_probs, wl2) ->
                        let uu____25427 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____25427 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____25440 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____25441 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____25440 s uu____25441 in
                             let uu____25442 =
                               let uu____25471 =
                                 let uu____25472 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____25472.FStar_Syntax_Syntax.n in
                               match uu____25471 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____25531 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____25531 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____25594 =
                                          let uu____25613 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____25613
                                            (fun uu____25716 ->
                                               match uu____25716 with
                                               | (l1, l2) ->
                                                   let uu____25789 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____25789)) in
                                        (match uu____25594 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____25894 ->
                                   let uu____25895 =
                                     let uu____25900 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____25900) in
                                   FStar_Errors.raise_error uu____25895 r in
                             (match uu____25442 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____25973 =
                                    let uu____25980 =
                                      let uu____25981 =
                                        let uu____25982 =
                                          let uu____25989 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____25989,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____25982 in
                                      [uu____25981] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____25980
                                      (fun b ->
                                         let uu____26005 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____26006 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____26007 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____26005 uu____26006
                                           uu____26007) r in
                                  (match uu____25973 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3724_26015 = wl3 in
                                         {
                                           attempting =
                                             (uu___3724_26015.attempting);
                                           wl_deferred =
                                             (uu___3724_26015.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3724_26015.wl_deferred_to_tac);
                                           ctr = (uu___3724_26015.ctr);
                                           defer_ok =
                                             (uu___3724_26015.defer_ok);
                                           smt_ok = (uu___3724_26015.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3724_26015.umax_heuristic_ok);
                                           tcenv = (uu___3724_26015.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3724_26015.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____26040 =
                                                  let uu____26047 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____26047, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____26040) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____26064 =
                                         let f_sort_is =
                                           let uu____26074 =
                                             let uu____26077 =
                                               let uu____26078 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____26078.FStar_Syntax_Syntax.sort in
                                             let uu____26087 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____26088 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____26077 uu____26087 r
                                               uu____26088 in
                                           FStar_All.pipe_right uu____26074
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____26093 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____26129 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____26129 with
                                                  | (ps, wl5) ->
                                                      ((let uu____26151 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____26151
                                                        then
                                                          let uu____26152 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____26153 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____26152
                                                            uu____26153
                                                        else ());
                                                       (let uu____26155 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____26155
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____26093 in
                                       (match uu____26064 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____26179 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____26179
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____26180 =
                                              let g_sort_is =
                                                let uu____26190 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____26191 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____26190 r uu____26191 in
                                              let uu____26192 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____26228 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____26228 with
                                                       | (ps, wl6) ->
                                                           ((let uu____26250
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____26250
                                                             then
                                                               let uu____26251
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____26252
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____26251
                                                                 uu____26252
                                                             else ());
                                                            (let uu____26254
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____26254
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____26192 in
                                            (match uu____26180 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____26280 =
                                                     let uu____26285 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____26286 =
                                                       let uu____26287 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____26287 in
                                                     (uu____26285,
                                                       uu____26286) in
                                                   match uu____26280 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____26315 =
                                                     let uu____26318 =
                                                       let uu____26321 =
                                                         let uu____26324 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____26324 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____26321 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____26318 in
                                                   ret_sub_prob ::
                                                     uu____26315 in
                                                 let guard =
                                                   let guard =
                                                     let uu____26345 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____26345 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____26356 =
                                                     let uu____26359 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____26362 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____26362)
                                                       uu____26359 in
                                                   solve_prob orig
                                                     uu____26356 [] wl6 in
                                                 let uu____26363 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____26363))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____26388 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____26390 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____26390]
               | x -> x in
             let c12 =
               let uu___3782_26393 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3782_26393.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3782_26393.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3782_26393.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3782_26393.FStar_Syntax_Syntax.flags)
               } in
             let uu____26394 =
               let uu____26399 =
                 FStar_All.pipe_right
                   (let uu___3785_26401 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3785_26401.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3785_26401.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3785_26401.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3785_26401.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____26399
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____26394
               (fun uu____26415 ->
                  match uu____26415 with
                  | (c, g) ->
                      let uu____26422 =
                        let uu____26423 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____26423 in
                      if uu____26422
                      then
                        let uu____26424 =
                          let uu____26429 =
                            let uu____26430 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____26431 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____26430 uu____26431 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____26429) in
                        FStar_Errors.raise_error uu____26424 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____26433 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____26435 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____26435))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____26433
           then
             let uu____26436 =
               mklstr
                 (fun uu____26443 ->
                    let uu____26444 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____26445 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____26444 uu____26445) in
             giveup env uu____26436 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_26451 ->
                        match uu___29_26451 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____26452 -> false)) in
              let uu____26453 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____26483)::uu____26484,
                   (wp2, uu____26486)::uu____26487) -> (wp1, wp2)
                | uu____26560 ->
                    let uu____26585 =
                      let uu____26590 =
                        let uu____26591 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____26592 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____26591 uu____26592 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____26590) in
                    FStar_Errors.raise_error uu____26585
                      env.FStar_TypeChecker_Env.range in
              match uu____26453 with
              | (wpc1, wpc2) ->
                  let uu____26599 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____26599
                  then
                    let uu____26600 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____26600 wl
                  else
                    (let uu____26602 =
                       let uu____26609 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____26609 in
                     match uu____26602 with
                     | (c2_decl, qualifiers) ->
                         let uu____26630 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____26630
                         then
                           let c1_repr =
                             let uu____26634 =
                               let uu____26635 =
                                 let uu____26636 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____26636 in
                               let uu____26637 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26635 uu____26637 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26634 in
                           let c2_repr =
                             let uu____26639 =
                               let uu____26640 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____26641 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26640 uu____26641 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26639 in
                           let uu____26642 =
                             let uu____26647 =
                               let uu____26648 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____26649 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____26648 uu____26649 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____26647 in
                           (match uu____26642 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____26653 = attempt [prob] wl2 in
                                solve env uu____26653)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____26670 = lift_c1 () in
                                   FStar_All.pipe_right uu____26670
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____26692 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____26692
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____26696 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____26696 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____26702 =
                                       let uu____26703 =
                                         let uu____26720 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____26723 =
                                           let uu____26734 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____26734; wpc1_2] in
                                         (uu____26720, uu____26723) in
                                       FStar_Syntax_Syntax.Tm_app uu____26703 in
                                     FStar_Syntax_Syntax.mk uu____26702 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____26782 =
                                      let uu____26783 =
                                        let uu____26800 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____26803 =
                                          let uu____26814 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____26823 =
                                            let uu____26834 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____26834; wpc1_2] in
                                          uu____26814 :: uu____26823 in
                                        (uu____26800, uu____26803) in
                                      FStar_Syntax_Syntax.Tm_app uu____26783 in
                                    FStar_Syntax_Syntax.mk uu____26782 r)) in
                            (let uu____26888 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____26888
                             then
                               let uu____26889 =
                                 let uu____26890 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____26890 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____26889
                             else ());
                            (let uu____26892 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____26892 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____26900 =
                                     let uu____26903 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____26906 ->
                                          FStar_Pervasives_Native.Some
                                            uu____26906) uu____26903 in
                                   solve_prob orig uu____26900 [] wl1 in
                                 let uu____26907 = attempt [base_prob] wl2 in
                                 solve env uu____26907))))) in
        let uu____26908 = FStar_Util.physical_equality c1 c2 in
        if uu____26908
        then
          let uu____26909 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____26909
        else
          ((let uu____26912 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____26912
            then
              let uu____26913 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____26914 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____26913
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____26914
            else ());
           (let uu____26916 =
              let uu____26925 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____26928 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____26925, uu____26928) in
            match uu____26916 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____26946),
                    FStar_Syntax_Syntax.Total (t2, uu____26948)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____26965 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____26965 wl
                 | (FStar_Syntax_Syntax.GTotal uu____26966,
                    FStar_Syntax_Syntax.Total uu____26967) ->
                     let uu____26984 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____26984 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____26986),
                    FStar_Syntax_Syntax.Total (t2, uu____26988)) ->
                     let uu____27005 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27005 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____27007),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27009)) ->
                     let uu____27026 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27026 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27028),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27030)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____27047 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27047 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27049),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27051)) ->
                     let uu____27068 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____27068 orig
                 | (FStar_Syntax_Syntax.GTotal uu____27069,
                    FStar_Syntax_Syntax.Comp uu____27070) ->
                     let uu____27079 =
                       let uu___3909_27082 = problem in
                       let uu____27085 =
                         let uu____27086 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27086 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3909_27082.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27085;
                         FStar_TypeChecker_Common.relation =
                           (uu___3909_27082.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3909_27082.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3909_27082.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3909_27082.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3909_27082.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3909_27082.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3909_27082.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3909_27082.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27079 wl
                 | (FStar_Syntax_Syntax.Total uu____27087,
                    FStar_Syntax_Syntax.Comp uu____27088) ->
                     let uu____27097 =
                       let uu___3909_27100 = problem in
                       let uu____27103 =
                         let uu____27104 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27104 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3909_27100.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27103;
                         FStar_TypeChecker_Common.relation =
                           (uu___3909_27100.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3909_27100.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3909_27100.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3909_27100.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3909_27100.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3909_27100.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3909_27100.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3909_27100.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27097 wl
                 | (FStar_Syntax_Syntax.Comp uu____27105,
                    FStar_Syntax_Syntax.GTotal uu____27106) ->
                     let uu____27115 =
                       let uu___3921_27118 = problem in
                       let uu____27121 =
                         let uu____27122 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27122 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3921_27118.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3921_27118.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3921_27118.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27121;
                         FStar_TypeChecker_Common.element =
                           (uu___3921_27118.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3921_27118.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3921_27118.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3921_27118.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3921_27118.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3921_27118.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27115 wl
                 | (FStar_Syntax_Syntax.Comp uu____27123,
                    FStar_Syntax_Syntax.Total uu____27124) ->
                     let uu____27133 =
                       let uu___3921_27136 = problem in
                       let uu____27139 =
                         let uu____27140 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27140 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3921_27136.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3921_27136.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3921_27136.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27139;
                         FStar_TypeChecker_Common.element =
                           (uu___3921_27136.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3921_27136.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3921_27136.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3921_27136.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3921_27136.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3921_27136.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27133 wl
                 | (FStar_Syntax_Syntax.Comp uu____27141,
                    FStar_Syntax_Syntax.Comp uu____27142) ->
                     let uu____27143 =
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
                     if uu____27143
                     then
                       let uu____27144 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____27144 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27148 =
                            let uu____27153 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____27153
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27159 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____27160 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____27159, uu____27160)) in
                          match uu____27148 with
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
                           (let uu____27167 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____27167
                            then
                              let uu____27168 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____27169 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____27168 uu____27169
                            else ());
                           (let uu____27171 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____27171
                            then solve_layered_sub c12 c22
                            else
                              (let uu____27173 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____27173 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____27176 =
                                     mklstr
                                       (fun uu____27183 ->
                                          let uu____27184 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____27185 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____27184 uu____27185) in
                                   giveup env uu____27176 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____27192 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____27192 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____27233 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____27233 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____27251 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27279 ->
                match uu____27279 with
                | (u1, u2) ->
                    let uu____27286 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____27287 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____27286 uu____27287)) in
      FStar_All.pipe_right uu____27251 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial, [], (uu____27314, [])) when
          let uu____27339 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____27339 -> "{}"
      | uu____27340 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27363 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____27363
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____27383 =
              FStar_List.map
                (fun uu____27394 ->
                   match uu____27394 with
                   | (msg, x) ->
                       let uu____27401 =
                         let uu____27402 = prob_to_string env x in
                         Prims.op_Hat ": " uu____27402 in
                       Prims.op_Hat msg uu____27401) defs in
            FStar_All.pipe_right uu____27383 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____27406 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____27407 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____27408 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____27406 uu____27407 uu____27408 imps
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
                  let uu____27461 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____27461
                  then
                    let uu____27462 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____27463 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27462
                      (rel_to_string rel) uu____27463
                  else "TOP" in
                let uu____27465 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____27465 with
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
              let uu____27523 =
                let uu____27526 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____27529 ->
                     FStar_Pervasives_Native.Some uu____27529) uu____27526 in
              FStar_Syntax_Syntax.new_bv uu____27523 t1 in
            let uu____27530 =
              let uu____27535 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27535 in
            match uu____27530 with | (p, wl1) -> (p, x, wl1)
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
        (let uu____27606 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____27606
         then
           let uu____27607 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____27607
         else ());
        (let uu____27611 =
           FStar_Util.record_time (fun uu____27617 -> solve env probs) in
         match uu____27611 with
         | (sol, ms) ->
             ((let uu____27629 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____27629
               then
                 let uu____27630 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____27630
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____27643 =
                     FStar_Util.record_time
                       (fun uu____27649 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____27643 with
                    | ((), ms1) ->
                        ((let uu____27660 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____27660
                          then
                            let uu____27661 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____27661
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____27672 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____27672
                     then
                       let uu____27673 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____27673
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
          ((let uu____27697 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____27697
            then
              let uu____27698 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27698
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____27702 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____27702
             then
               let uu____27703 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27703
             else ());
            (let f2 =
               let uu____27706 =
                 let uu____27707 = FStar_Syntax_Util.unmeta f1 in
                 uu____27707.FStar_Syntax_Syntax.n in
               match uu____27706 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27711 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4041_27712 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4041_27712.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4041_27712.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4041_27712.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4041_27712.FStar_TypeChecker_Common.implicits)
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
            let uu____27763 =
              let uu____27764 =
                let uu____27765 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____27766 ->
                       FStar_TypeChecker_Common.NonTrivial uu____27766) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____27765;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____27764 in
            FStar_All.pipe_left
              (fun uu____27773 -> FStar_Pervasives_Native.Some uu____27773)
              uu____27763
let with_guard_no_simp :
  'uuuuuu27782 .
    'uuuuuu27782 ->
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
            let uu____27831 =
              let uu____27832 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____27833 ->
                     FStar_TypeChecker_Common.NonTrivial uu____27833) in
              {
                FStar_TypeChecker_Common.guard_f = uu____27832;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____27831
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
          (let uu____27863 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____27863
           then
             let uu____27864 = FStar_Syntax_Print.term_to_string t1 in
             let uu____27865 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____27864
               uu____27865
           else ());
          (let uu____27867 =
             let uu____27872 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____27872 in
           match uu____27867 with
           | (prob, wl) ->
               let g =
                 let uu____27880 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____27890 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____27880 in
               ((let uu____27912 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____27912
                 then
                   let uu____27913 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____27913
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
        let uu____27930 = try_teq true env t1 t2 in
        match uu____27930 with
        | FStar_Pervasives_Native.None ->
            ((let uu____27934 = FStar_TypeChecker_Env.get_range env in
              let uu____27935 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____27934 uu____27935);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____27942 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____27942
              then
                let uu____27943 = FStar_Syntax_Print.term_to_string t1 in
                let uu____27944 = FStar_Syntax_Print.term_to_string t2 in
                let uu____27945 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____27943
                  uu____27944 uu____27945
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
        (let uu____27965 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____27965
         then
           let uu____27966 = FStar_Syntax_Print.term_to_string t1 in
           let uu____27967 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____27966
             uu____27967
         else ());
        (let uu____27969 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____27969 with
         | (prob, x, wl) ->
             let g =
               let uu____27984 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____27994 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____27984 in
             ((let uu____28016 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____28016
               then
                 let uu____28017 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____28017
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____28022 =
                     let uu____28023 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____28023 g1 in
                   FStar_Pervasives_Native.Some uu____28022)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____28044 = FStar_TypeChecker_Env.get_range env in
          let uu____28045 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____28044 uu____28045
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
        (let uu____28070 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____28070
         then
           let uu____28071 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____28072 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28071 uu____28072
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28075 =
           let uu____28082 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28082 "sub_comp" in
         match uu____28075 with
         | (prob, wl) ->
             let wl1 =
               let uu___4114_28092 = wl in
               {
                 attempting = (uu___4114_28092.attempting);
                 wl_deferred = (uu___4114_28092.wl_deferred);
                 wl_deferred_to_tac = (uu___4114_28092.wl_deferred_to_tac);
                 ctr = (uu___4114_28092.ctr);
                 defer_ok = (uu___4114_28092.defer_ok);
                 smt_ok = (uu___4114_28092.smt_ok);
                 umax_heuristic_ok = (uu___4114_28092.umax_heuristic_ok);
                 tcenv = (uu___4114_28092.tcenv);
                 wl_implicits = (uu___4114_28092.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____28095 =
                 FStar_Util.record_time
                   (fun uu____28106 ->
                      let uu____28107 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____28117 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____28107) in
               match uu____28095 with
               | (r, ms) ->
                   ((let uu____28147 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____28147
                     then
                       let uu____28148 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____28149 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____28150 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28148 uu____28149
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28150
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
      fun uu____28179 ->
        match uu____28179 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28222 =
                 let uu____28227 =
                   let uu____28228 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____28229 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28228 uu____28229 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28227) in
               let uu____28230 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____28222 uu____28230) in
            let equiv v v' =
              let uu____28242 =
                let uu____28247 = FStar_Syntax_Subst.compress_univ v in
                let uu____28248 = FStar_Syntax_Subst.compress_univ v' in
                (uu____28247, uu____28248) in
              match uu____28242 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28271 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____28301 = FStar_Syntax_Subst.compress_univ v in
                      match uu____28301 with
                      | FStar_Syntax_Syntax.U_unif uu____28308 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28339 ->
                                    match uu____28339 with
                                    | (u, v') ->
                                        let uu____28348 = equiv v v' in
                                        if uu____28348
                                        then
                                          let uu____28351 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____28351 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____28367 -> [])) in
            let uu____28372 =
              let wl =
                let uu___4157_28376 = empty_worklist env in
                {
                  attempting = (uu___4157_28376.attempting);
                  wl_deferred = (uu___4157_28376.wl_deferred);
                  wl_deferred_to_tac = (uu___4157_28376.wl_deferred_to_tac);
                  ctr = (uu___4157_28376.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4157_28376.smt_ok);
                  umax_heuristic_ok = (uu___4157_28376.umax_heuristic_ok);
                  tcenv = (uu___4157_28376.tcenv);
                  wl_implicits = (uu___4157_28376.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4157_28376.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28394 ->
                      match uu____28394 with
                      | (lb, v) ->
                          let uu____28401 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____28401 with
                           | USolved wl1 -> ()
                           | uu____28403 -> fail lb v))) in
            let rec check_ineq uu____28413 =
              match uu____28413 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____28422) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____28449,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____28451,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____28464) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____28471, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____28479 -> false) in
            let uu____28484 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28499 ->
                      match uu____28499 with
                      | (u, v) ->
                          let uu____28506 = check_ineq (u, v) in
                          if uu____28506
                          then true
                          else
                            ((let uu____28509 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____28509
                              then
                                let uu____28510 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____28511 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____28510
                                  uu____28511
                              else ());
                             false))) in
            if uu____28484
            then ()
            else
              ((let uu____28515 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____28515
                then
                  ((let uu____28517 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28517);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28527 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28527))
                else ());
               (let uu____28537 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28537))
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
          let fail uu____28611 =
            match uu____28611 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4235_28636 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4235_28636.attempting);
              wl_deferred = (uu___4235_28636.wl_deferred);
              wl_deferred_to_tac = (uu___4235_28636.wl_deferred_to_tac);
              ctr = (uu___4235_28636.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4235_28636.umax_heuristic_ok);
              tcenv = (uu___4235_28636.tcenv);
              wl_implicits = (uu___4235_28636.wl_implicits);
              repr_subcomp_allowed = (uu___4235_28636.repr_subcomp_allowed)
            } in
          (let uu____28638 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____28638
           then
             let uu____28639 = FStar_Util.string_of_bool defer_ok in
             let uu____28640 = wl_to_string wl in
             let uu____28641 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____28639 uu____28640 uu____28641
           else ());
          (let g1 =
             let uu____28644 = solve_and_commit env wl fail in
             match uu____28644 with
             | FStar_Pervasives_Native.Some
                 (uu____28653::uu____28654, uu____28655, uu____28656) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4252_28686 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4252_28686.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4252_28686.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____28691 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____28703 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____28703
             then
               let uu____28704 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____28704
             else ());
            (let uu___4260_28706 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4260_28706.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4260_28706.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4260_28706.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4260_28706.FStar_TypeChecker_Common.implicits)
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
          (let uu____28781 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____28781
           then
             let uu____28782 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____28782
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4277_28786 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4277_28786.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4277_28786.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4277_28786.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4277_28786.FStar_TypeChecker_Common.implicits)
             } in
           let uu____28787 =
             let uu____28788 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____28788 in
           if uu____28787
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____28796 = FStar_TypeChecker_Env.get_range env in
                      let uu____28797 =
                        let uu____28798 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____28798 in
                      FStar_Errors.diag uu____28796 uu____28797)
                   else ();
                   (let vc1 =
                      let uu____28801 =
                        let uu____28804 =
                          let uu____28805 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____28805 in
                        FStar_Pervasives_Native.Some uu____28804 in
                      FStar_Profiling.profile
                        (fun uu____28807 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____28801 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____28809 = FStar_TypeChecker_Env.get_range env in
                       let uu____28810 =
                         let uu____28811 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____28811 in
                       FStar_Errors.diag uu____28809 uu____28810)
                    else ();
                    (let uu____28814 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____28814 "discharge_guard'" env vc1);
                    (let uu____28815 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____28815 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____28822 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____28823 =
                                 let uu____28824 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____28824 in
                               FStar_Errors.diag uu____28822 uu____28823)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____28829 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____28830 =
                                 let uu____28831 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____28831 in
                               FStar_Errors.diag uu____28829 uu____28830)
                            else ();
                            (let vcs =
                               let uu____28842 = FStar_Options.use_tactics () in
                               if uu____28842
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____28862 ->
                                      (let uu____28864 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____28865 -> ()) uu____28864);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____28908 ->
                                               match uu____28908 with
                                               | (env1, goal, opts) ->
                                                   let uu____28924 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____28924, opts)))))
                               else
                                 (let uu____28926 =
                                    let uu____28933 = FStar_Options.peek () in
                                    (env, vc2, uu____28933) in
                                  [uu____28926]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____28966 ->
                                     match uu____28966 with
                                     | (env1, goal, opts) ->
                                         let uu____28976 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____28976 with
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
                                                 (let uu____28983 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____28984 =
                                                    let uu____28985 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____28986 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____28985 uu____28986 in
                                                  FStar_Errors.diag
                                                    uu____28983 uu____28984)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____28989 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____28990 =
                                                    let uu____28991 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____28991 in
                                                  FStar_Errors.diag
                                                    uu____28989 uu____28990)
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
      let uu____29005 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____29005 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____29012 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29012
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____29023 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____29023 with
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
        let uu____29049 = try_teq false env t1 t2 in
        match uu____29049 with
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
             let uu____29092 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____29092 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____29102 =
                   let uu____29103 = FStar_Syntax_Subst.compress t_norm in
                   uu____29103.FStar_Syntax_Syntax.n in
                 (match uu____29102 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____29109 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29109
                        (fun uu____29112 ->
                           FStar_Pervasives_Native.Some uu____29112)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____29114) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____29119 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29119
                        (fun uu____29122 ->
                           FStar_Pervasives_Native.Some uu____29122)
                  | uu____29123 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____29133 =
                      let uu____29134 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____29134 FStar_Util.is_none in
                    if uu____29133
                    then
                      let uu____29139 = imp_value imp in
                      match uu____29139 with
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
        let uu____29160 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____29160 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____29178 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____29178 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____29182 ->
                       let uu____29183 =
                         let uu____29184 = FStar_Syntax_Subst.compress r in
                         uu____29184.FStar_Syntax_Syntax.n in
                       (match uu____29183 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____29188)
                            -> unresolved ctx_u'
                        | uu____29205 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____29225 = acc in
              match uu____29225 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____29232 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____29232 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____29245 = hd in
                       (match uu____29245 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____29251 = unresolved ctx_u in
                               if uu____29251
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____29260 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____29260
                                       then
                                         let uu____29261 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____29261
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____29267 =
                                           teq_nosmt env1 t tm in
                                         match uu____29267 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4422_29276 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4422_29276.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4422_29276.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4422_29276.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4422_29276.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4422_29276.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4422_29276.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4422_29276.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4425_29278 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4425_29278.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4425_29278.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4425_29278.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____29279 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4430_29285 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4430_29285.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4430_29285.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4430_29285.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4430_29285.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4430_29285.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4430_29285.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4430_29285.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4430_29285.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4430_29285.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4430_29285.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4430_29285.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4430_29285.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4430_29285.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4430_29285.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4430_29285.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4430_29285.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4430_29285.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4430_29285.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4430_29285.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4430_29285.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4430_29285.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4430_29285.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4430_29285.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4430_29285.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4430_29285.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4430_29285.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4430_29285.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4430_29285.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4430_29285.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4430_29285.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4430_29285.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4430_29285.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4430_29285.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4430_29285.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4430_29285.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4430_29285.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4430_29285.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4435_29288 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4435_29288.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4435_29288.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4435_29288.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4435_29288.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4435_29288.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4435_29288.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4435_29288.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4435_29288.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4435_29288.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4435_29288.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4435_29288.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4435_29288.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4435_29288.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4435_29288.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4435_29288.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4435_29288.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4435_29288.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4435_29288.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4435_29288.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4435_29288.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4435_29288.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4435_29288.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4435_29288.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4435_29288.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4435_29288.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4435_29288.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4435_29288.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4435_29288.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4435_29288.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4435_29288.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4435_29288.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4435_29288.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____29291 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29291
                                     then
                                       let uu____29292 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____29293 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____29294 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____29295 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____29292 uu____29293 uu____29294
                                         reason uu____29295
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4441_29299 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____29306 =
                                               let uu____29315 =
                                                 let uu____29322 =
                                                   let uu____29323 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____29324 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____29325 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____29323 uu____29324
                                                     uu____29325 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____29322, r) in
                                               [uu____29315] in
                                             FStar_Errors.add_errors
                                               uu____29306);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____29339 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____29349 ->
                                                 let uu____29350 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____29351 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____29352 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____29350 uu____29351
                                                   reason uu____29352)) env2
                                           g1 true in
                                       match uu____29339 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4453_29354 = g in
            let uu____29355 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4453_29354.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4453_29354.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4453_29354.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4453_29354.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____29355
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____29367 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29367
       then
         let uu____29368 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____29368
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
      (let uu____29391 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29391
       then
         let uu____29392 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____29392
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____29396 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____29397 -> ()) uu____29396
       | imp::uu____29399 ->
           let uu____29402 =
             let uu____29407 =
               let uu____29408 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____29409 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____29408 uu____29409
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29407) in
           FStar_Errors.raise_error uu____29402
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29425 = teq env t1 t2 in
        force_trivial_guard env uu____29425
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29441 = teq_nosmt env t1 t2 in
        match uu____29441 with
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
          (let uu____29471 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____29471
           then
             let uu____29472 =
               let uu____29473 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____29473
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____29479 = FStar_Syntax_Print.term_to_string t1 in
             let uu____29480 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____29472
               uu____29479 uu____29480
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4491_29492 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4491_29492.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4491_29492.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4491_29492.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4491_29492.FStar_TypeChecker_Common.implicits)
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
        (let uu____29527 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29527
         then
           let uu____29528 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29529 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29528
             uu____29529
         else ());
        (let uu____29531 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29531 with
         | (prob, x, wl) ->
             let g =
               let uu____29550 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29560 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29550 in
             ((let uu____29582 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____29582
               then
                 let uu____29583 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____29584 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____29585 =
                   let uu____29586 = FStar_Util.must g in
                   guard_to_string env uu____29586 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29583 uu____29584 uu____29585
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
        let uu____29620 = check_subtyping env t1 t2 in
        match uu____29620 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29639 =
              let uu____29640 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____29640 g in
            FStar_Pervasives_Native.Some uu____29639
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29658 = check_subtyping env t1 t2 in
        match uu____29658 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29677 =
              let uu____29678 =
                let uu____29679 = FStar_Syntax_Syntax.mk_binder x in
                [uu____29679] in
              FStar_TypeChecker_Env.close_guard env uu____29678 g in
            FStar_Pervasives_Native.Some uu____29677
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____29716 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29716
         then
           let uu____29717 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29718 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____29717
             uu____29718
         else ());
        (let uu____29720 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29720 with
         | (prob, x, wl) ->
             let g =
               let uu____29735 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____29745 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29735 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____29770 =
                      let uu____29771 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____29771] in
                    FStar_TypeChecker_Env.close_guard env uu____29770 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29808 = subtype_nosmt env t1 t2 in
        match uu____29808 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)