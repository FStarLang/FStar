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
                (let uu____3202 = norm_refinement env t12 in
                 match uu____3202 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1, phi1);
                     FStar_Syntax_Syntax.pos = uu____3217;
                     FStar_Syntax_Syntax.vars = uu____3218;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3242 =
                       let uu____3243 = FStar_Syntax_Print.term_to_string tt in
                       let uu____3244 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3243 uu____3244 in
                     failwith uu____3242)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3258 = FStar_Syntax_Util.unfold_lazy i in
              aux norm uu____3258
          | FStar_Syntax_Syntax.Tm_uinst uu____3259 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3294 =
                   let uu____3295 = FStar_Syntax_Subst.compress t1' in
                   uu____3295.FStar_Syntax_Syntax.n in
                 match uu____3294 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3310 -> aux true t1'
                 | uu____3317 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3332 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3361 =
                   let uu____3362 = FStar_Syntax_Subst.compress t1' in
                   uu____3362.FStar_Syntax_Syntax.n in
                 match uu____3361 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3377 -> aux true t1'
                 | uu____3384 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3399 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3444 =
                   let uu____3445 = FStar_Syntax_Subst.compress t1' in
                   uu____3445.FStar_Syntax_Syntax.n in
                 match uu____3444 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3460 -> aux true t1'
                 | uu____3467 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3482 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3497 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3512 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3527 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3542 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3571 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3604 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3625 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3652 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3679 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3716 ->
              let uu____3723 =
                let uu____3724 = FStar_Syntax_Print.term_to_string t12 in
                let uu____3725 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3724 uu____3725 in
              failwith uu____3723
          | FStar_Syntax_Syntax.Tm_ascribed uu____3738 ->
              let uu____3765 =
                let uu____3766 = FStar_Syntax_Print.term_to_string t12 in
                let uu____3767 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3766 uu____3767 in
              failwith uu____3765
          | FStar_Syntax_Syntax.Tm_delayed uu____3780 ->
              let uu____3795 =
                let uu____3796 = FStar_Syntax_Print.term_to_string t12 in
                let uu____3797 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3796 uu____3797 in
              failwith uu____3795
          | FStar_Syntax_Syntax.Tm_unknown ->
              let uu____3810 =
                let uu____3811 = FStar_Syntax_Print.term_to_string t12 in
                let uu____3812 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3811 uu____3812 in
              failwith uu____3810 in
        let uu____3825 = whnf env t1 in aux false uu____3825
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
      let uu____3866 = base_and_refinement env t in
      FStar_All.pipe_right uu____3866 FStar_Pervasives_Native.fst
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t ->
    let uu____3906 = FStar_Syntax_Syntax.null_bv t in
    (uu____3906, FStar_Syntax_Util.t_true)
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta ->
    fun env ->
      fun t ->
        let uu____3930 = base_and_refinement_maybe_delta delta env t in
        match uu____3930 with
        | (t_base, refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x, phi) -> (x, phi))
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____3989 ->
    match uu____3989 with
    | (t_base, refopt) ->
        let uu____4020 =
          match refopt with
          | FStar_Pervasives_Native.Some (y, phi) -> (y, phi)
          | FStar_Pervasives_Native.None -> trivial_refinement t_base in
        (match uu____4020 with
         | (y, phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl -> fun prob -> prob_to_string wl.tcenv prob
let (wl_to_string : worklist -> Prims.string) =
  fun wl ->
    let uu____4058 =
      let uu____4061 =
        let uu____4064 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4087 ->
                  match uu____4087 with | (uu____4094, uu____4095, x) -> x)) in
        FStar_List.append wl.attempting uu____4064 in
      FStar_List.map (wl_prob_to_string wl) uu____4061 in
    FStar_All.pipe_right uu____4058 (FStar_String.concat "\n\t")
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
  fun uu____4143 ->
    match uu____4143 with
    | Flex (uu____4144, u, uu____4146) ->
        u.FStar_Syntax_Syntax.ctx_uvar_reason
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4151 ->
    match uu____4151 with
    | Flex (uu____4152, c, args) ->
        let uu____4155 = print_ctx_uvar c in
        let uu____4156 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "%s [%s]" uu____4155 uu____4156
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____4162 = FStar_Syntax_Util.head_and_args t in
    match uu____4162 with
    | (head, _args) ->
        let uu____4205 =
          let uu____4206 = FStar_Syntax_Subst.compress head in
          uu____4206.FStar_Syntax_Syntax.n in
        (match uu____4205 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4209 -> true
         | uu____4222 -> false)
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t ->
    let uu____4228 = FStar_Syntax_Util.head_and_args t in
    match uu____4228 with
    | (head, _args) ->
        let uu____4271 =
          let uu____4272 = FStar_Syntax_Subst.compress head in
          uu____4272.FStar_Syntax_Syntax.n in
        (match uu____4271 with
         | FStar_Syntax_Syntax.Tm_uvar (u, uu____4276) -> u
         | uu____4293 -> failwith "Not a flex-uvar")
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0 ->
    fun wl ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x in
        let t_x' = FStar_Syntax_Subst.subst' s t_x in
        let uu____4325 =
          let uu____4326 = FStar_Syntax_Subst.compress t_x' in
          uu____4326.FStar_Syntax_Syntax.n in
        match uu____4325 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____4330 -> false in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____4343 -> true in
      let uu____4344 = FStar_Syntax_Util.head_and_args t0 in
      match uu____4344 with
      | (head, args) ->
          let uu____4391 =
            let uu____4392 = FStar_Syntax_Subst.compress head in
            uu____4392.FStar_Syntax_Syntax.n in
          (match uu____4391 with
           | FStar_Syntax_Syntax.Tm_uvar (uv, ([], uu____4400)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv, uu____4416) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
               let uu____4457 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma in
               (match uu____4457 with
                | (gamma_aff, new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____4484 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff in
                         let uu____4488 =
                           let uu____4495 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma in
                           let uu____4504 =
                             let uu____4507 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                             FStar_Syntax_Util.arrow dom_binders uu____4507 in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____4495
                             uu____4504
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta in
                         (match uu____4488 with
                          | (v, t_v, wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____4542 ->
                                     match uu____4542 with
                                     | (x, i) ->
                                         let uu____4561 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         (uu____4561, i)) dom_binders in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  t0.FStar_Syntax_Syntax.pos in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____4591 ->
                                       match uu____4591 with
                                       | (a, i) ->
                                           let uu____4610 =
                                             FStar_Syntax_Subst.subst' s a in
                                           (uu____4610, i)) args_sol in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    t0.FStar_Syntax_Syntax.pos in
                                (t, wl1))))))
           | uu____4620 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t ->
    let uu____4630 = FStar_Syntax_Util.head_and_args t in
    match uu____4630 with
    | (head, args) ->
        let uu____4673 =
          let uu____4674 = FStar_Syntax_Subst.compress head in
          uu____4674.FStar_Syntax_Syntax.n in
        (match uu____4673 with
         | FStar_Syntax_Syntax.Tm_uvar (uv, s) -> Flex (t, uv, args)
         | uu____4695 -> failwith "Not a flex-uvar")
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t ->
    fun wl ->
      let uu____4714 = ensure_no_uvar_subst t wl in
      match uu____4714 with
      | (t1, wl1) ->
          let uu____4725 = destruct_flex_t' t1 in (uu____4725, wl1)
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k ->
    fun ys ->
      fun t ->
        let uu____4741 =
          let uu____4764 =
            let uu____4765 = FStar_Syntax_Subst.compress k in
            uu____4765.FStar_Syntax_Syntax.n in
          match uu____4764 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4846 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____4846)
              else
                (let uu____4880 = FStar_Syntax_Util.abs_formals t in
                 match uu____4880 with
                 | (ys', t1, uu____4913) ->
                     let uu____4918 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____4918))
          | uu____4957 ->
              let uu____4958 =
                let uu____4963 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____4963) in
              ((ys, t), uu____4958) in
        match uu____4741 with
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
                 let uu____5056 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____5056 c in
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
               (let uu____5130 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel") in
                if uu____5130
                then
                  let uu____5131 = FStar_Util.string_of_int (p_pid prob) in
                  let uu____5132 = print_ctx_uvar uv in
                  let uu____5133 = FStar_Syntax_Print.term_to_string phi1 in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5131 uu____5132 uu____5133
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0)) in
                (let uu____5139 =
                   let uu____5140 = FStar_Util.string_of_int (p_pid prob) in
                   Prims.op_Hat "solve_prob'.sol." uu____5140 in
                 let uu____5141 =
                   let uu____5144 = p_scope prob in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5144 in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5139 uu____5141 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2) in
             let uv = p_guard_uvar prob in
             let fail uu____5177 =
               let uu____5178 =
                 let uu____5179 = FStar_Syntax_Print.ctx_uvar_to_string uv in
                 let uu____5180 =
                   FStar_Syntax_Print.term_to_string (p_guard prob) in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5179 uu____5180 in
               failwith uu____5178 in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5244 ->
                       match uu____5244 with
                       | (a, i) ->
                           let uu____5265 =
                             let uu____5266 = FStar_Syntax_Subst.compress a in
                             uu____5266.FStar_Syntax_Syntax.n in
                           (match uu____5265 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5292 -> (fail (); [])))) in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob) in
               let uu____5302 =
                 let uu____5303 = is_flex g in Prims.op_Negation uu____5303 in
               if uu____5302
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____5307 = destruct_flex_t g wl in
                  match uu____5307 with
                  | (Flex (uu____5312, uv1, args), wl1) ->
                      ((let uu____5317 = args_as_binders args in
                        assign_solution uu____5317 uv1 phi);
                       wl1)) in
             commit uvis;
             (let uu___762_5319 = wl1 in
              {
                attempting = (uu___762_5319.attempting);
                wl_deferred = (uu___762_5319.wl_deferred);
                wl_deferred_to_tac = (uu___762_5319.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___762_5319.defer_ok);
                smt_ok = (uu___762_5319.smt_ok);
                umax_heuristic_ok = (uu___762_5319.umax_heuristic_ok);
                tcenv = (uu___762_5319.tcenv);
                wl_implicits = (uu___762_5319.wl_implicits);
                repr_subcomp_allowed = (uu___762_5319.repr_subcomp_allowed)
              }))
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid ->
    fun sol ->
      fun wl ->
        (let uu____5340 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel") in
         if uu____5340
         then
           let uu____5341 = FStar_Util.string_of_int pid in
           let uu____5342 = uvis_to_string wl.tcenv sol in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5341 uu____5342
         else ());
        commit sol;
        (let uu___770_5345 = wl in
         {
           attempting = (uu___770_5345.attempting);
           wl_deferred = (uu___770_5345.wl_deferred);
           wl_deferred_to_tac = (uu___770_5345.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___770_5345.defer_ok);
           smt_ok = (uu___770_5345.smt_ok);
           umax_heuristic_ok = (uu___770_5345.umax_heuristic_ok);
           tcenv = (uu___770_5345.tcenv);
           wl_implicits = (uu___770_5345.wl_implicits);
           repr_subcomp_allowed = (uu___770_5345.repr_subcomp_allowed)
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
          (let uu____5377 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel") in
           if uu____5377
           then
             let uu____5378 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____5379 = uvis_to_string wl.tcenv uvis in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5378 uu____5379
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
        let uu____5400 = FStar_Syntax_Free.uvars t in
        FStar_All.pipe_right uu____5400 FStar_Util.set_elements in
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
      let uu____5434 = occurs uk t in
      match uu____5434 with
      | (uvars, occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5463 =
                 let uu____5464 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head in
                 let uu____5465 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5464 uu____5465 in
               FStar_Pervasives_Native.Some uu____5463) in
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
          let uu____5570 = FStar_Syntax_Syntax.bv_eq b b' in
          if uu____5570
          then
            let uu____5579 = maximal_prefix bs_tail bs'_tail in
            (match uu____5579 with | (pfx, rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5629 -> ([], (bs, bs'))
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      FStar_List.fold_left
        (fun g1 ->
           fun uu____5685 ->
             match uu____5685 with
             | (x, uu____5697) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      let uu____5714 = FStar_List.last bs in
      match uu____5714 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some (x, uu____5738) ->
          let uu____5749 =
            FStar_Util.prefix_until
              (fun uu___18_5764 ->
                 match uu___18_5764 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5766 -> false) g in
          (match uu____5749 with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some (uu____5779, bx, rest) -> bx ::
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
            let uu____5825 =
              maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
                src.FStar_Syntax_Syntax.ctx_uvar_binders in
            match uu____5825 with
            | (pfx, uu____5835) ->
                let g =
                  gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx in
                let aux t f =
                  let uu____5863 =
                    let uu____5870 =
                      let uu____5871 =
                        FStar_Syntax_Print.uvar_to_string
                          src.FStar_Syntax_Syntax.ctx_uvar_head in
                      Prims.op_Hat "restricted " uu____5871 in
                    new_uvar uu____5870 wl
                      src.FStar_Syntax_Syntax.ctx_uvar_range g pfx t
                      src.FStar_Syntax_Syntax.ctx_uvar_should_check
                      src.FStar_Syntax_Syntax.ctx_uvar_meta in
                  match uu____5863 with
                  | (uu____5872, src', wl1) ->
                      ((let uu____5876 = f src' in
                        FStar_Syntax_Util.set_uvar
                          src.FStar_Syntax_Syntax.ctx_uvar_head uu____5876);
                       wl1) in
                let bs1 =
                  FStar_All.pipe_right bs
                    (FStar_List.filter
                       (fun uu____5911 ->
                          match uu____5911 with
                          | (bv1, uu____5919) ->
                              (FStar_All.pipe_right
                                 src.FStar_Syntax_Syntax.ctx_uvar_binders
                                 (FStar_List.existsb
                                    (fun uu____5941 ->
                                       match uu____5941 with
                                       | (bv2, uu____5949) ->
                                           FStar_Syntax_Syntax.bv_eq bv1 bv2)))
                                &&
                                (let uu____5955 =
                                   FStar_All.pipe_right pfx
                                     (FStar_List.existsb
                                        (fun uu____5973 ->
                                           match uu____5973 with
                                           | (bv2, uu____5981) ->
                                               FStar_Syntax_Syntax.bv_eq bv1
                                                 bv2)) in
                                 Prims.op_Negation uu____5955))) in
                if (FStar_List.length bs1) = Prims.int_zero
                then
                  aux src.FStar_Syntax_Syntax.ctx_uvar_typ (fun src' -> src')
                else
                  (let uu____5995 =
                     let uu____5996 =
                       let uu____5999 =
                         let uu____6002 =
                           FStar_All.pipe_right
                             src.FStar_Syntax_Syntax.ctx_uvar_typ
                             (env.FStar_TypeChecker_Env.universe_of env) in
                         FStar_All.pipe_right uu____6002
                           (fun uu____6005 ->
                              FStar_Pervasives_Native.Some uu____6005) in
                       FStar_All.pipe_right uu____5999
                         (FStar_Syntax_Syntax.mk_Total'
                            src.FStar_Syntax_Syntax.ctx_uvar_typ) in
                     FStar_All.pipe_right uu____5996
                       (FStar_Syntax_Util.arrow bs1) in
                   aux uu____5995
                     (fun src' ->
                        let uu____6015 =
                          let uu____6016 =
                            FStar_All.pipe_right bs1
                              FStar_Syntax_Syntax.binders_to_names in
                          FStar_All.pipe_right uu____6016
                            (FStar_List.map FStar_Syntax_Syntax.as_arg) in
                        FStar_Syntax_Syntax.mk_Tm_app src' uu____6015
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
                 | uu____6141 -> out) FStar_Syntax_Syntax.no_names g in
        let uu____6142 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6206 ->
                  fun uu____6207 ->
                    match (uu____6206, uu____6207) with
                    | ((isect, isect_set), (x, imp)) ->
                        let uu____6310 =
                          let uu____6311 = FStar_Util.set_mem x v1_set in
                          FStar_All.pipe_left Prims.op_Negation uu____6311 in
                        if uu____6310
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6340 =
                             FStar_Util.set_is_subset_of fvs isect_set in
                           if uu____6340
                           then
                             let uu____6355 = FStar_Util.set_add x isect_set in
                             (((x, imp) :: isect), uu____6355)
                           else (isect, isect_set))) ([], ctx_binders)) in
        match uu____6142 with | (isect, uu____6404) -> FStar_List.rev isect
let binders_eq :
  'uuuuuu6439 'uuuuuu6440 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6439) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6440) Prims.list -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6497 ->
              fun uu____6498 ->
                match (uu____6497, uu____6498) with
                | ((a, uu____6516), (b, uu____6518)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let name_exists_in_binders :
  'uuuuuu6533 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6533) Prims.list -> Prims.bool
  =
  fun x ->
    fun bs ->
      FStar_Util.for_some
        (fun uu____6563 ->
           match uu____6563 with
           | (y, uu____6569) -> FStar_Syntax_Syntax.bv_eq x y) bs
let pat_vars :
  'uuuuuu6578 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6578) Prims.list ->
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
                   let uu____6740 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu____6740
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6770 -> FStar_Pervasives_Native.None) in
        aux [] args
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu____6817 -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch _0 -> true | uu____6854 -> false
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee -> match projectee with | HeadMatch _0 -> _0
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | FullMatch -> true | uu____6866 -> false
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_6871 ->
    match uu___19_6871 with
    | MisMatch (d1, d2) ->
        let uu____6882 =
          let uu____6883 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu____6884 =
            let uu____6885 =
              let uu____6886 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.op_Hat uu____6886 ")" in
            Prims.op_Hat ") (" uu____6885 in
          Prims.op_Hat uu____6883 uu____6884 in
        Prims.op_Hat "MisMatch (" uu____6882
    | HeadMatch u ->
        let uu____6888 = FStar_Util.string_of_bool u in
        Prims.op_Hat "HeadMatch " uu____6888
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___20_6893 ->
    match uu___20_6893 with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu____6908 -> HeadMatch false
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____6921 =
            (let uu____6926 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
             let uu____6927 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu____6926 = uu____6927) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) in
          if uu____6921 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____6930 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____6930 with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6941 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____6964 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6973 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6991 = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu____6991
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6992 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6993 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6994 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7007 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7020 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____7044) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____7050, uu____7051) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu____7093) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7118;
             FStar_Syntax_Syntax.index = uu____7119;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____7121)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7128 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7129 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7130 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7145 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7152 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7172 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____7172
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
           { FStar_Syntax_Syntax.blob = uu____7190;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7191;
             FStar_Syntax_Syntax.ltyp = uu____7192;
             FStar_Syntax_Syntax.rng = uu____7193;_},
           uu____7194) ->
            let uu____7205 = FStar_Syntax_Util.unlazy t11 in
            head_matches env uu____7205 t21
        | (uu____7206, FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7207;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7208;
             FStar_Syntax_Syntax.ltyp = uu____7209;
             FStar_Syntax_Syntax.rng = uu____7210;_})
            ->
            let uu____7221 = FStar_Syntax_Util.unlazy t21 in
            head_matches env t11 uu____7221
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7224 = FStar_Syntax_Syntax.bv_eq x y in
            if uu____7224
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7232 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____7232
            then FullMatch
            else
              (let uu____7234 =
                 let uu____7243 =
                   let uu____7246 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____7246 in
                 let uu____7247 =
                   let uu____7250 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____7250 in
                 (uu____7243, uu____7247) in
               MisMatch uu____7234)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu____7256),
           FStar_Syntax_Syntax.Tm_uinst (g, uu____7258)) ->
            let uu____7267 = head_matches env f g in
            FStar_All.pipe_right uu____7267 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           uu____7268) -> HeadMatch true
        | (uu____7269, FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify)) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7272 = FStar_Const.eq_const c d in
            if uu____7272
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu____7279),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu____7281)) ->
            let uu____7314 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head in
            if uu____7314
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7321),
           FStar_Syntax_Syntax.Tm_refine (y, uu____7323)) ->
            let uu____7332 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7332 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7334), uu____7335) ->
            let uu____7340 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____7340 head_match
        | (uu____7341, FStar_Syntax_Syntax.Tm_refine (x, uu____7343)) ->
            let uu____7348 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7348 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7349,
           FStar_Syntax_Syntax.Tm_type uu____7350) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow uu____7351,
           FStar_Syntax_Syntax.Tm_arrow uu____7352) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7382),
           FStar_Syntax_Syntax.Tm_app (head', uu____7384)) ->
            let uu____7433 = head_matches env head head' in
            FStar_All.pipe_right uu____7433 head_match
        | (FStar_Syntax_Syntax.Tm_app (head, uu____7435), uu____7436) ->
            let uu____7461 = head_matches env head t21 in
            FStar_All.pipe_right uu____7461 head_match
        | (uu____7462, FStar_Syntax_Syntax.Tm_app (head, uu____7464)) ->
            let uu____7489 = head_matches env t11 head in
            FStar_All.pipe_right uu____7489 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7490, FStar_Syntax_Syntax.Tm_let
           uu____7491) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match uu____7516,
           FStar_Syntax_Syntax.Tm_match uu____7517) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7562, FStar_Syntax_Syntax.Tm_abs
           uu____7563) -> HeadMatch true
        | uu____7600 ->
            let uu____7605 =
              let uu____7614 = delta_depth_of_term env t11 in
              let uu____7617 = delta_depth_of_term env t21 in
              (uu____7614, uu____7617) in
            MisMatch uu____7605
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
              let uu____7685 = unrefine env t in
              FStar_Syntax_Util.head_of uu____7685 in
            (let uu____7687 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7687
             then
               let uu____7688 = FStar_Syntax_Print.term_to_string t in
               let uu____7689 = FStar_Syntax_Print.term_to_string head in
               FStar_Util.print2 "Head of %s is %s\n" uu____7688 uu____7689
             else ());
            (let uu____7691 =
               let uu____7692 = FStar_Syntax_Util.un_uinst head in
               uu____7692.FStar_Syntax_Syntax.n in
             match uu____7691 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7698 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 (match uu____7698 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu____7712 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta") in
                        if uu____7712
                        then
                          let uu____7713 =
                            FStar_Syntax_Print.term_to_string head in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7713
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7715 ->
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
                      let uu____7730 =
                        let uu____7731 = FStar_Syntax_Util.eq_tm t t' in
                        uu____7731 = FStar_Syntax_Util.Equal in
                      if uu____7730
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____7736 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta") in
                          if uu____7736
                          then
                            let uu____7737 =
                              FStar_Syntax_Print.term_to_string t in
                            let uu____7738 =
                              FStar_Syntax_Print.term_to_string t' in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____7737
                              uu____7738
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____7740 -> FStar_Pervasives_Native.None) in
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
            (let uu____7878 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____7878
             then
               let uu____7879 = FStar_Syntax_Print.term_to_string t11 in
               let uu____7880 = FStar_Syntax_Print.term_to_string t21 in
               let uu____7881 = string_of_match_result r in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____7879
                 uu____7880 uu____7881
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
               let uu____7905 =
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
               match uu____7905 with
               | (t12, t22) -> aux retry (n_delta + Prims.int_one) t12 t22 in
             let reduce_both_and_try_again d r1 =
               let uu____7950 = FStar_TypeChecker_Common.decr_delta_depth d in
               match uu____7950 with
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
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____7982),
                  uu____7983)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8001 =
                      let uu____8010 = maybe_inline t11 in
                      let uu____8013 = maybe_inline t21 in
                      (uu____8010, uu____8013) in
                    match uu____8001 with
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
                 (uu____8050, FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8051))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8069 =
                      let uu____8078 = maybe_inline t11 in
                      let uu____8081 = maybe_inline t21 in
                      (uu____8078, uu____8081) in
                    match uu____8069 with
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
             | MisMatch uu____8130 -> fail n_delta r t11 t21
             | uu____8139 -> success n_delta r t11 t21) in
          let r = aux true Prims.int_zero t1 t2 in
          (let uu____8152 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu____8152
           then
             let uu____8153 = FStar_Syntax_Print.term_to_string t1 in
             let uu____8154 = FStar_Syntax_Print.term_to_string t2 in
             let uu____8155 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             let uu____8162 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8174 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must in
                  FStar_All.pipe_right uu____8174
                    (fun uu____8208 ->
                       match uu____8208 with
                       | (t11, t21) ->
                           let uu____8215 =
                             FStar_Syntax_Print.term_to_string t11 in
                           let uu____8216 =
                             let uu____8217 =
                               FStar_Syntax_Print.term_to_string t21 in
                             Prims.op_Hat "; " uu____8217 in
                           Prims.op_Hat uu____8215 uu____8216)) in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8153 uu____8154 uu____8155 uu____8162
           else ());
          r
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____8229 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____8229 FStar_Pervasives_Native.fst
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8242 ->
    match uu___21_8242 with
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
      let uu___1279_8279 = p in
      let uu____8282 = whnf tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____8283 = whnf tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1279_8279.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8282;
        FStar_TypeChecker_Common.relation =
          (uu___1279_8279.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8283;
        FStar_TypeChecker_Common.element =
          (uu___1279_8279.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1279_8279.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1279_8279.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1279_8279.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1279_8279.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1279_8279.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8297 = compress_tprob tcenv p1 in
          FStar_All.pipe_right uu____8297
            (fun uu____8302 -> FStar_TypeChecker_Common.TProb uu____8302)
      | FStar_TypeChecker_Common.CProb uu____8303 -> p
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv ->
    fun pr ->
      let prob =
        let uu____8325 = compress_prob tcenv pr in
        FStar_All.pipe_right uu____8325 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8333 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____8333 with
           | (lh, lhs_args) ->
               let uu____8380 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____8380 with
                | (rh, rhs_args) ->
                    let uu____8427 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8440,
                         FStar_Syntax_Syntax.Tm_uvar uu____8441) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8530 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8557, uu____8558)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8573, FStar_Syntax_Syntax.Tm_uvar uu____8574)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8589,
                         FStar_Syntax_Syntax.Tm_arrow uu____8590) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1330_8620 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1330_8620.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1330_8620.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1330_8620.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1330_8620.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1330_8620.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1330_8620.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1330_8620.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1330_8620.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1330_8620.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8623,
                         FStar_Syntax_Syntax.Tm_type uu____8624) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1330_8640 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1330_8640.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1330_8640.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1330_8640.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1330_8640.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1330_8640.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1330_8640.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1330_8640.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1330_8640.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1330_8640.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type uu____8643,
                         FStar_Syntax_Syntax.Tm_uvar uu____8644) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1330_8660 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1330_8660.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1330_8660.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1330_8660.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1330_8660.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1330_8660.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1330_8660.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1330_8660.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1330_8660.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1330_8660.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____8663, FStar_Syntax_Syntax.Tm_uvar uu____8664)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8679, uu____8680)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____8695, FStar_Syntax_Syntax.Tm_uvar uu____8696)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____8711, uu____8712) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu____8427 with
                     | (rank, tp1) ->
                         let uu____8725 =
                           FStar_All.pipe_right
                             (let uu___1350_8729 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1350_8729.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1350_8729.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1350_8729.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1350_8729.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1350_8729.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1350_8729.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1350_8729.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1350_8729.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1350_8729.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____8732 ->
                                FStar_TypeChecker_Common.TProb uu____8732) in
                         (rank, uu____8725))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____8736 =
            FStar_All.pipe_right
              (let uu___1354_8740 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1354_8740.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1354_8740.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1354_8740.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1354_8740.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1354_8740.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1354_8740.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1354_8740.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1354_8740.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1354_8740.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____8743 -> FStar_TypeChecker_Common.CProb uu____8743) in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____8736)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    let rec aux uu____8802 probs =
      match uu____8802 with
      | (min_rank, min, out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some p,
                   FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____8883 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____8904 = rank wl.tcenv hd in
               (match uu____8904 with
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
                      (let uu____8963 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____8967 = FStar_Option.get min_rank in
                            rank_less_than rank1 uu____8967) in
                       if uu____8963
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
          let uu____9035 = FStar_Syntax_Util.head_and_args t in
          match uu____9035 with
          | (hd, uu____9053) ->
              let uu____9078 =
                let uu____9079 = FStar_Syntax_Subst.compress hd in
                uu____9079.FStar_Syntax_Syntax.n in
              (match uu____9078 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu____9083) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9117 ->
                           match uu____9117 with
                           | (y, uu____9125) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9147 ->
                                       match uu____9147 with
                                       | (x, uu____9155) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9160 -> false) in
        let uu____9161 = rank tcenv p in
        match uu____9161 with
        | (r, p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9168 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9200 -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | USolved _0 -> true | uu____9213 -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UFailed _0 -> true | uu____9226 -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s -> let uu____9238 = FStar_Thunk.mkv s in UFailed uu____9238
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu____9249 = mklstr s in UFailed uu____9249
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
                        let uu____9294 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____9294 with
                        | (k, uu____9300) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9312 -> false)))
            | uu____9313 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu____9365 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2 -> FStar_Syntax_Util.eq_univs uv1 uv2)) in
                        if uu____9365 then uv1 :: uvs else uvs) []) in
            let filter =
              FStar_List.filter
                (fun u ->
                   let uu____9385 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u' -> FStar_Syntax_Util.eq_univs u u')) in
                   Prims.op_Negation uu____9385) in
            let uu____9390 = filter u12 in
            let uu____9393 = filter u22 in (uu____9390, uu____9393) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9423 = filter_out_common_univs us1 us2 in
                   (match uu____9423 with
                    | (us11, us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13, u23::us23) ->
                                let uu____9482 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23 in
                                (match uu____9482 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9485 -> USolved wl1 in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9501 ->
                               let uu____9502 =
                                 FStar_Syntax_Print.univ_to_string u12 in
                               let uu____9503 =
                                 FStar_Syntax_Print.univ_to_string u22 in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9502 uu____9503))
               | (FStar_Syntax_Syntax.U_max us, u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9527 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9527 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | (u', FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____9553 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____9553 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | uu____9556 ->
                   ufailed_thunk
                     (fun uu____9567 ->
                        let uu____9568 =
                          FStar_Syntax_Print.univ_to_string u12 in
                        let uu____9569 =
                          FStar_Syntax_Print.univ_to_string u22 in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____9568 uu____9569 msg)) in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____9570, uu____9571) ->
              let uu____9572 =
                let uu____9573 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9574 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9573 uu____9574 in
              failwith uu____9572
          | (FStar_Syntax_Syntax.U_unknown, uu____9575) ->
              let uu____9576 =
                let uu____9577 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9578 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9577 uu____9578 in
              failwith uu____9576
          | (uu____9579, FStar_Syntax_Syntax.U_bvar uu____9580) ->
              let uu____9581 =
                let uu____9582 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9583 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9582 uu____9583 in
              failwith uu____9581
          | (uu____9584, FStar_Syntax_Syntax.U_unknown) ->
              let uu____9585 =
                let uu____9586 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____9587 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____9586 uu____9587 in
              failwith uu____9585
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              let uu____9590 =
                let uu____9591 = FStar_Ident.string_of_id x in
                let uu____9592 = FStar_Ident.string_of_id y in
                uu____9591 = uu____9592 in
              if uu____9590
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu____9618 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____9618
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu____9634 = occurs_univ v1 u3 in
              if uu____9634
              then
                let uu____9635 =
                  let uu____9636 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9637 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9636 uu____9637 in
                try_umax_components u11 u21 uu____9635
              else
                (let uu____9639 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9639)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____9653 = occurs_univ v1 u3 in
              if uu____9653
              then
                let uu____9654 =
                  let uu____9655 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____9656 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____9655 uu____9656 in
                try_umax_components u11 u21 uu____9654
              else
                (let uu____9658 = extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____9658)
          | (FStar_Syntax_Syntax.U_max uu____9659, uu____9660) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9666 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9666
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____9668, FStar_Syntax_Syntax.U_max uu____9669) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____9675 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____9675
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____9677,
             FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____9678,
             FStar_Syntax_Syntax.U_name uu____9679) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ
             uu____9680) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name
             uu____9681) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9682,
             FStar_Syntax_Syntax.U_succ uu____9683) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____9684,
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
      let uu____9784 = bc1 in
      match uu____9784 with
      | (bs1, mk_cod1) ->
          let uu____9828 = bc2 in
          (match uu____9828 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu____9939 = aux xs ys in
                     (match uu____9939 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu____10022 =
                       let uu____10029 = mk_cod1 xs in ([], uu____10029) in
                     let uu____10032 =
                       let uu____10039 = mk_cod2 ys in ([], uu____10039) in
                     (uu____10022, uu____10032) in
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
                  let uu____10107 = FStar_Syntax_Syntax.bv_to_name t in
                  FStar_Syntax_Util.mk_has_type t11 uu____10107 t21
              | FStar_Pervasives_Native.None ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11 in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11 in
                  let uu____10110 =
                    let uu____10111 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Util.mk_has_type t11 uu____10111 t21 in
                  FStar_Syntax_Util.mk_forall u_x x uu____10110 in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB ->
                let uu____10116 = has_type_guard t1 t2 in (uu____10116, wl)
            | FStar_TypeChecker_Common.SUBINV ->
                let uu____10117 = has_type_guard t2 t1 in (uu____10117, wl)
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_10122 ->
    match uu___22_10122 with
    | Flex (uu____10123, uu____10124, []) -> true
    | uu____10133 -> false
let (should_defer_flex_to_user_tac :
  FStar_TypeChecker_Env.env -> worklist -> flex_t -> Prims.bool) =
  fun env ->
    fun wl ->
      fun f ->
        let uu____10149 = f in
        match uu____10149 with
        | Flex (uu____10150, u, uu____10152) ->
            let b =
              FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                wl.tcenv u in
            ((let uu____10155 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ResolveImplicitsHook") in
              if uu____10155
              then
                let uu____10156 =
                  FStar_Syntax_Print.ctx_uvar_to_string_no_reason u in
                let uu____10157 = FStar_Util.string_of_bool b in
                FStar_Util.print2
                  "Rel.should_defer_flex_to_user_tac for %s returning %s\n"
                  uu____10156 uu____10157
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
      let uu____10181 = f in
      match uu____10181 with
      | Flex
          (uu____10188,
           { FStar_Syntax_Syntax.ctx_uvar_head = uu____10189;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10190;
             FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
             FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____10193;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____10194;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____10195;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____10196;_},
           args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10260 ->
                 match uu____10260 with
                 | (y, uu____10268) -> FStar_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu____10422 =
                  let uu____10437 =
                    let uu____10440 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10440 in
                  ((FStar_List.rev pat_binders), uu____10437) in
                FStar_Pervasives_Native.Some uu____10422
            | (uu____10473, []) ->
                let uu____10504 =
                  let uu____10519 =
                    let uu____10522 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____10522 in
                  ((FStar_List.rev pat_binders), uu____10519) in
                FStar_Pervasives_Native.Some uu____10504
            | ((formal, formal_imp)::formals1, (a, a_imp)::args2) ->
                let uu____10613 =
                  let uu____10614 = FStar_Syntax_Subst.compress a in
                  uu____10614.FStar_Syntax_Syntax.n in
                (match uu____10613 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____10634 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders) in
                     if uu____10634
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1695_10661 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1695_10661.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1695_10661.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          } in
                        let subst =
                          let uu____10665 =
                            let uu____10666 =
                              let uu____10673 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              (formal, uu____10673) in
                            FStar_Syntax_Syntax.NT uu____10666 in
                          [uu____10665] in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1 in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res in
                        aux
                          (((let uu___1701_10689 = x1 in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1701_10689.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1701_10689.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____10690 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([], args2) ->
                let uu____10730 =
                  let uu____10737 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStar_Syntax_Util.arrow_formals uu____10737 in
                (match uu____10730 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____10796 ->
                          aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____10821 ->
               let uu____10822 = FStar_Syntax_Util.arrow_formals t_hd in
               (match uu____10822 with
                | (formals, t_res) -> aux [] formals t_res args))
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu____11151 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel") in
       if uu____11151
       then
         let uu____11152 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11152
       else ());
      (let uu____11155 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace") in
       if uu____11155
       then
         let uu____11156 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11156
       else ());
      (let uu____11158 = next_prob probs in
       match uu____11158 with
       | FStar_Pervasives_Native.Some (hd, tl, rank1) ->
           let probs1 =
             let uu___1728_11185 = probs in
             {
               attempting = tl;
               wl_deferred = (uu___1728_11185.wl_deferred);
               wl_deferred_to_tac = (uu___1728_11185.wl_deferred_to_tac);
               ctr = (uu___1728_11185.ctr);
               defer_ok = (uu___1728_11185.defer_ok);
               smt_ok = (uu___1728_11185.smt_ok);
               umax_heuristic_ok = (uu___1728_11185.umax_heuristic_ok);
               tcenv = (uu___1728_11185.tcenv);
               wl_implicits = (uu___1728_11185.wl_implicits);
               repr_subcomp_allowed = (uu___1728_11185.repr_subcomp_allowed)
             } in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11193 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs in
                 if uu____11193
                 then
                   let uu____11194 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                   solve env uu____11194
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
                           (let uu___1740_11199 = tp in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1740_11199.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1740_11199.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1740_11199.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1740_11199.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1740_11199.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1740_11199.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1740_11199.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1740_11199.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1740_11199.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None ->
           (match probs.wl_deferred with
            | [] ->
                let uu____11217 =
                  let uu____11224 = as_deferred probs.wl_deferred_to_tac in
                  ([], uu____11224, (probs.wl_implicits)) in
                Success uu____11217
            | uu____11229 ->
                let uu____11238 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11297 ->
                          match uu____11297 with
                          | (c, uu____11305, uu____11306) -> c < probs.ctr)) in
                (match uu____11238 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11347 =
                            let uu____11354 = as_deferred probs.wl_deferred in
                            let uu____11355 =
                              as_deferred probs.wl_deferred_to_tac in
                            (uu____11354, uu____11355, (probs.wl_implicits)) in
                          Success uu____11347
                      | uu____11356 ->
                          let uu____11365 =
                            let uu___1754_11366 = probs in
                            let uu____11367 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____11386 ->
                                      match uu____11386 with
                                      | (uu____11393, uu____11394, y) -> y)) in
                            {
                              attempting = uu____11367;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1754_11366.wl_deferred_to_tac);
                              ctr = (uu___1754_11366.ctr);
                              defer_ok = (uu___1754_11366.defer_ok);
                              smt_ok = (uu___1754_11366.smt_ok);
                              umax_heuristic_ok =
                                (uu___1754_11366.umax_heuristic_ok);
                              tcenv = (uu___1754_11366.tcenv);
                              wl_implicits = (uu___1754_11366.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1754_11366.repr_subcomp_allowed)
                            } in
                          solve env uu____11365))))
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
            let uu____11401 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____11401 with
            | USolved wl1 ->
                let uu____11403 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____11403
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____11406 = defer_lit "" orig wl1 in
                solve env uu____11406
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
                  let uu____11456 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____11456 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____11459 -> ufailed_simple "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____11471;
                  FStar_Syntax_Syntax.vars = uu____11472;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____11475;
                  FStar_Syntax_Syntax.vars = uu____11476;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____11488, uu____11489) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____11496, FStar_Syntax_Syntax.Tm_uinst uu____11497) ->
                failwith "Impossible: expect head symbols to match"
            | uu____11504 -> USolved wl
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
            ((let uu____11514 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____11514
              then
                let uu____11515 = prob_to_string env orig in
                let uu____11516 = FStar_Thunk.force msg in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____11515 uu____11516
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
          (let uu____11524 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____11524
           then
             let uu____11525 = prob_to_string env orig in
             FStar_Util.print1 "\n\t\tDeferring %s to a tactic\n" uu____11525
           else ());
          (let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
           let wl2 =
             let uu___1838_11529 = wl1 in
             let uu____11530 =
               let uu____11539 =
                 let uu____11546 = FStar_Thunk.mkv reason in
                 ((wl1.ctr), uu____11546, orig) in
               uu____11539 :: (wl1.wl_deferred_to_tac) in
             {
               attempting = (uu___1838_11529.attempting);
               wl_deferred = (uu___1838_11529.wl_deferred);
               wl_deferred_to_tac = uu____11530;
               ctr = (uu___1838_11529.ctr);
               defer_ok = (uu___1838_11529.defer_ok);
               smt_ok = (uu___1838_11529.smt_ok);
               umax_heuristic_ok = (uu___1838_11529.umax_heuristic_ok);
               tcenv = (uu___1838_11529.tcenv);
               wl_implicits = (uu___1838_11529.wl_implicits);
               repr_subcomp_allowed = (uu___1838_11529.repr_subcomp_allowed)
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
                let uu____11569 = FStar_Syntax_Util.head_and_args t in
                match uu____11569 with
                | (head, uu____11591) ->
                    let uu____11616 =
                      let uu____11617 = FStar_Syntax_Subst.compress head in
                      uu____11617.FStar_Syntax_Syntax.n in
                    (match uu____11616 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu____11625) ->
                         let uu____11642 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu____11642,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____11643 -> (false, "")) in
              let uu____11644 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu____11644 with
               | (l1, r1) ->
                   let uu____11651 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu____11651 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____11659 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl in
                           solve env uu____11659)))
          | uu____11660 ->
              let uu____11661 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu____11661
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
               let uu____11745 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu____11745 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu____11798 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu____11798
                then
                  let uu____11799 = FStar_Syntax_Print.term_to_string t1 in
                  let uu____11800 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____11799 uu____11800
                else ());
               (let uu____11802 = head_matches_delta env1 wl2 t1 t2 in
                match uu____11802 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu____11847 = eq_prob t1 t2 wl2 in
                         (match uu____11847 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11868 ->
                         let uu____11877 = eq_prob t1 t2 wl2 in
                         (match uu____11877 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu____11926 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu____11941 =
                                 FStar_Syntax_Subst.compress t11 in
                               let uu____11942 =
                                 FStar_Syntax_Subst.compress t21 in
                               (uu____11941, uu____11942)
                           | FStar_Pervasives_Native.None ->
                               let uu____11947 =
                                 FStar_Syntax_Subst.compress t1 in
                               let uu____11948 =
                                 FStar_Syntax_Subst.compress t2 in
                               (uu____11947, uu____11948) in
                         (match uu____11926 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11979 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu____11979 with
                                | (t1_hd, t1_args) ->
                                    let uu____12024 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu____12024 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12088 =
                                              let uu____12095 =
                                                let uu____12106 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu____12106 :: t1_args in
                                              let uu____12123 =
                                                let uu____12132 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu____12132 :: t2_args in
                                              FStar_List.fold_left2
                                                (fun uu____12181 ->
                                                   fun uu____12182 ->
                                                     fun uu____12183 ->
                                                       match (uu____12181,
                                                               uu____12182,
                                                               uu____12183)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu____12233),
                                                          (a2, uu____12235))
                                                           ->
                                                           let uu____12272 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu____12272
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12095
                                                uu____12123 in
                                            match uu____12088 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  let uu___1941_12298 = wl4 in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1941_12298.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1941_12298.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1941_12298.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1941_12298.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1941_12298.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____12306 =
                                                  solve env1 wl' in
                                                (match uu____12306 with
                                                 | Success
                                                     (uu____12309,
                                                      defer_to_tac, imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____12313 =
                                                         extend_wl wl4
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu____12313))
                                                 | Failed uu____12314 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu____12346 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu____12346 with
                                | (t1_base, p1_opt) ->
                                    let uu____12381 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu____12381 with
                                     | (t2_base, p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____12479 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu____12479
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
                                               let uu____12527 =
                                                 op phi11 phi21 in
                                               refine x1 uu____12527
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
                                               let uu____12557 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12557
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
                                               let uu____12587 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12587
                                           | uu____12590 -> t_base in
                                         let uu____12607 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu____12607 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____12621 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu____12621, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu____12628 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu____12628 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu____12663 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu____12663 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu____12698 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu____12698
                                                         with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu____12722 = combine t11 t21 wl2 in
                              (match uu____12722 with
                               | (t12, ps, wl3) ->
                                   ((let uu____12755 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu____12755
                                     then
                                       let uu____12756 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____12756
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu____12795 ts1 =
               match uu____12795 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12858 = pairwise out t wl2 in
                        (match uu____12858 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2)) in
             let uu____12894 =
               let uu____12905 = FStar_List.hd ts in (uu____12905, [], wl1) in
             let uu____12914 = FStar_List.tl ts in
             aux uu____12894 uu____12914 in
           let uu____12921 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu____12921 with
           | (this_flex, this_rigid) ->
               let uu____12945 =
                 let uu____12946 = FStar_Syntax_Subst.compress this_rigid in
                 uu____12946.FStar_Syntax_Syntax.n in
               (match uu____12945 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu____12971 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu____12971
                    then
                      let uu____12972 = destruct_flex_t this_flex wl in
                      (match uu____12972 with
                       | (flex, wl1) ->
                           let uu____12979 = quasi_pattern env flex in
                           (match uu____12979 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu____12997 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____12997
                                  then
                                    let uu____12998 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12998
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13001 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2051_13004 = tp in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2051_13004.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2051_13004.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2051_13004.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2051_13004.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2051_13004.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2051_13004.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2051_13004.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2051_13004.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2051_13004.FStar_TypeChecker_Common.rank)
                                }))] wl in
                       solve env uu____13001)
                | uu____13005 ->
                    ((let uu____13007 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____13007
                      then
                        let uu____13008 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13008
                      else ());
                     (let uu____13010 =
                        FStar_Syntax_Util.head_and_args this_flex in
                      match uu____13010 with
                      | (u, _args) ->
                          let uu____13053 =
                            let uu____13054 = FStar_Syntax_Subst.compress u in
                            uu____13054.FStar_Syntax_Syntax.n in
                          (match uu____13053 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu____13081 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu____13081 with
                                 | (u', uu____13099) ->
                                     let uu____13124 =
                                       let uu____13125 = whnf env u' in
                                       uu____13125.FStar_Syntax_Syntax.n in
                                     (match uu____13124 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13146 -> false) in
                               let uu____13147 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_13170 ->
                                         match uu___23_13170 with
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
                                              | uu____13179 -> false)
                                         | uu____13182 -> false)) in
                               (match uu____13147 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu____13196 = whnf env this_rigid in
                                      let uu____13197 =
                                        FStar_List.collect
                                          (fun uu___24_13203 ->
                                             match uu___24_13203 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13209 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu____13209]
                                             | uu____13211 -> [])
                                          bounds_probs in
                                      uu____13196 :: uu____13197 in
                                    let uu____13212 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu____13212 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu____13243 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu____13258 =
                                               let uu____13259 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu____13259.FStar_Syntax_Syntax.n in
                                             match uu____13258 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13271 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13271)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13280 -> bound in
                                           let uu____13281 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu____13281) in
                                         (match uu____13243 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13310 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu____13310
                                                then
                                                  let wl'1 =
                                                    let uu___2111_13312 = wl1 in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2111_13312.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2111_13312.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2111_13312.ctr);
                                                      defer_ok =
                                                        (uu___2111_13312.defer_ok);
                                                      smt_ok =
                                                        (uu___2111_13312.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2111_13312.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2111_13312.tcenv);
                                                      wl_implicits =
                                                        (uu___2111_13312.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2111_13312.repr_subcomp_allowed)
                                                    } in
                                                  let uu____13313 =
                                                    wl_to_string wl'1 in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13313
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____13316 =
                                                  solve_t env eq_prob
                                                    (let uu___2116_13318 =
                                                       wl' in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2116_13318.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2116_13318.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2116_13318.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2116_13318.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2116_13318.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2116_13318.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2116_13318.repr_subcomp_allowed)
                                                     }) in
                                                match uu____13316 with
                                                | Success
                                                    (uu____13319,
                                                     defer_to_tac, imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2123_13323 =
                                                        wl' in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2123_13323.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2123_13323.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2123_13323.ctr);
                                                        defer_ok =
                                                          (uu___2123_13323.defer_ok);
                                                        smt_ok =
                                                          (uu___2123_13323.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2123_13323.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2123_13323.tcenv);
                                                        wl_implicits =
                                                          (uu___2123_13323.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2123_13323.repr_subcomp_allowed)
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
                                                    let uu____13339 =
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
                                                    ((let uu____13350 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu____13350
                                                      then
                                                        let uu____13351 =
                                                          let uu____13352 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_All.pipe_right
                                                            uu____13352
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13351
                                                      else ());
                                                     (let uu____13358 =
                                                        let uu____13373 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu____13373) in
                                                      match uu____13358 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu____13395)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13421 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13421
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
                                                                  let uu____13438
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13438))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13463 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13463
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
                                                                    let uu____13481
                                                                    =
                                                                    let uu____13486
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13486 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13481
                                                                    [] wl2 in
                                                                  let uu____13491
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13491))))
                                                      | uu____13492 ->
                                                          let uu____13507 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env
                                                            uu____13507 p)))))))
                           | uu____13510 when flip ->
                               let uu____13511 =
                                 let uu____13512 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13513 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13512 uu____13513 in
                               failwith uu____13511
                           | uu____13514 ->
                               let uu____13515 =
                                 let uu____13516 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13517 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13516 uu____13517 in
                               failwith uu____13515)))))
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
                      (fun uu____13551 ->
                         match uu____13551 with
                         | (x, i) ->
                             let uu____13570 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             (uu____13570, i)) bs_lhs in
                  let uu____13573 = lhs in
                  match uu____13573 with
                  | Flex (uu____13574, u_lhs, uu____13576) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____13673 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____13683 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu____13683, univ) in
                          match uu____13673 with
                          | (k, univ) ->
                              let uu____13690 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2 in
                              (match uu____13690 with
                               | (uu____13707, u, wl3) ->
                                   let uu____13710 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu____13710, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____13736 =
                              let uu____13749 =
                                let uu____13760 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu____13760 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_List.fold_right
                                (fun uu____13811 ->
                                   fun uu____13812 ->
                                     match (uu____13811, uu____13812) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu____13913 =
                                           let uu____13920 =
                                             let uu____13923 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13923 in
                                           copy_uvar u_lhs [] uu____13920 wl2 in
                                         (match uu____13913 with
                                          | (uu____13952, t_a, wl3) ->
                                              let uu____13955 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu____13955 with
                                               | (uu____13974, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____13749
                                ([], wl1) in
                            (match uu____13736 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_14043 ->
                                        match uu___25_14043 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____14044 -> false
                                        | uu____14047 -> true) flags in
                                 let ct' =
                                   let uu___2242_14049 = ct in
                                   let uu____14050 =
                                     let uu____14053 = FStar_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu____14053 in
                                   let uu____14068 = FStar_List.tl out_args in
                                   let uu____14085 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2242_14049.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2242_14049.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14050;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14068;
                                     FStar_Syntax_Syntax.flags = uu____14085
                                   } in
                                 ((let uu___2245_14089 = c in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2245_14089.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2245_14089.FStar_Syntax_Syntax.vars)
                                   }), wl2)) in
                      let uu____14092 =
                        FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu____14092 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14130 =
                                   imitate_comp bs bs_terms c wl1 in
                                 (match uu____14130 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu____14141 =
                                          let uu____14146 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____14146) in
                                        TERM uu____14141 in
                                      let uu____14147 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu____14147 with
                                       | (sub_prob, wl3) ->
                                           let uu____14160 =
                                             let uu____14161 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu____14161 in
                                           solve env uu____14160))
                             | (x, imp)::formals2 ->
                                 let uu____14183 =
                                   let uu____14190 =
                                     let uu____14193 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____14193
                                       FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14190 wl1 in
                                 (match uu____14183 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu____14214 =
                                          let uu____14217 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some
                                            uu____14217 in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14214 u_x in
                                      let uu____14218 =
                                        let uu____14221 =
                                          let uu____14224 =
                                            let uu____14225 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y in
                                            (uu____14225, imp) in
                                          [uu____14224] in
                                        FStar_List.append bs_terms
                                          uu____14221 in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14218 formals2 wl2) in
                           let uu____14252 = occurs_check u_lhs arrow in
                           (match uu____14252 with
                            | (uu____14263, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14274 =
                                    mklstr
                                      (fun uu____14279 ->
                                         let uu____14280 =
                                           FStar_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14280) in
                                  giveup_or_defer env orig wl uu____14274
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
              (let uu____14309 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____14309
               then
                 let uu____14310 =
                   FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu____14311 =
                   FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14310 (rel_to_string (p_rel orig)) uu____14311
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu____14436 = rhs wl1 scope env1 subst in
                     (match uu____14436 with
                      | (rhs_prob, wl2) ->
                          ((let uu____14458 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu____14458
                            then
                              let uu____14459 = prob_to_string env1 rhs_prob in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14459
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1, imp)::xs1, (hd2, imp')::ys1) when
                     let uu____14532 = FStar_Syntax_Util.eq_aqual imp imp' in
                     uu____14532 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2315_14534 = hd1 in
                       let uu____14535 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2315_14534.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2315_14534.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14535
                       } in
                     let hd21 =
                       let uu___2318_14539 = hd2 in
                       let uu____14540 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2318_14539.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2318_14539.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14540
                       } in
                     let uu____14543 =
                       let uu____14548 =
                         FStar_All.pipe_left invert_rel (p_rel orig) in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____14548
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter" in
                     (match uu____14543 with
                      | (prob, wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                          let subst1 =
                            let uu____14569 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____14569 in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                          let uu____14573 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1 in
                          (match uu____14573 with
                           | (env3, FStar_Util.Inl (sub_probs, phi), wl3) ->
                               let phi1 =
                                 let uu____14641 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____14641 in
                               ((let uu____14659 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14659
                                 then
                                   let uu____14660 =
                                     FStar_Syntax_Print.term_to_string phi1 in
                                   let uu____14661 =
                                     FStar_Syntax_Print.bv_to_string hd12 in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____14660
                                     uu____14661
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____14690 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1) in
               let uu____14723 = aux wl [] env [] bs1 bs2 in
               match uu____14723 with
               | (env1, FStar_Util.Inr msg, wl1) -> giveup_lit env1 msg orig
               | (env1, FStar_Util.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu____14776 = attempt sub_probs wl2 in
                   solve env1 uu____14776)
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
            let uu___2356_14796 = wl in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2356_14796.wl_deferred_to_tac);
              ctr = (uu___2356_14796.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2356_14796.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2356_14796.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu____14804 = try_solve env wl' in
          match uu____14804 with
          | Success (uu____14805, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____14817 = compress_tprob wl.tcenv problem in
         solve_t' env uu____14817 wl)
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
            (let uu____14824 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Rel") in
             if uu____14824
             then FStar_Util.print_string "solve_t_flex_rigid_eq\n"
             else ());
            (let uu____14826 = should_defer_flex_to_user_tac env wl lhs in
             if uu____14826
             then defer_to_user_tac env orig (flex_reason lhs) wl
             else
               (let binders_as_bv_set bs =
                  let uu____14836 =
                    FStar_List.map FStar_Pervasives_Native.fst bs in
                  FStar_Util.as_set uu____14836 FStar_Syntax_Syntax.order_bv in
                let mk_solution env1 lhs1 bs rhs1 =
                  let uu____14870 = lhs1 in
                  match uu____14870 with
                  | Flex (uu____14873, ctx_u, uu____14875) ->
                      let sol =
                        match bs with
                        | [] -> rhs1
                        | uu____14883 ->
                            let uu____14884 = sn_binders env1 bs in
                            u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                              uu____14884 rhs1 in
                      [TERM (ctx_u, sol)] in
                let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                  (let uu____14932 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu____14932
                   then FStar_Util.print_string "try_quasi_pattern\n"
                   else ());
                  (let uu____14934 = quasi_pattern env1 lhs1 in
                   match uu____14934 with
                   | FStar_Pervasives_Native.None ->
                       ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                   | FStar_Pervasives_Native.Some (bs, uu____14964) ->
                       let uu____14969 = lhs1 in
                       (match uu____14969 with
                        | Flex (t_lhs, ctx_u, args) ->
                            let uu____14983 = occurs_check ctx_u rhs1 in
                            (match uu____14983 with
                             | (uvars, occurs_ok, msg) ->
                                 if Prims.op_Negation occurs_ok
                                 then
                                   let uu____15025 =
                                     let uu____15032 =
                                       let uu____15033 = FStar_Option.get msg in
                                       Prims.op_Hat
                                         "quasi-pattern, occurs-check failed: "
                                         uu____15033 in
                                     FStar_Util.Inl uu____15032 in
                                   (uu____15025, wl1)
                                 else
                                   (let fvs_lhs =
                                      binders_as_bv_set
                                        (FStar_List.append
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                           bs) in
                                    let fvs_rhs =
                                      FStar_Syntax_Free.names rhs1 in
                                    let uu____15055 =
                                      let uu____15056 =
                                        FStar_Util.set_is_subset_of fvs_rhs
                                          fvs_lhs in
                                      Prims.op_Negation uu____15056 in
                                    if uu____15055
                                    then
                                      ((FStar_Util.Inl
                                          "quasi-pattern, free names on the RHS are not included in the LHS"),
                                        wl1)
                                    else
                                      (let uu____15076 =
                                         let uu____15083 =
                                           mk_solution env1 lhs1 bs rhs1 in
                                         FStar_Util.Inr uu____15083 in
                                       let uu____15088 =
                                         restrict_all_uvars env1 ctx_u []
                                           uvars wl1 in
                                       (uu____15076, uu____15088)))))) in
                let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                  let uu____15137 = FStar_Syntax_Util.head_and_args rhs1 in
                  match uu____15137 with
                  | (rhs_hd, args) ->
                      let uu____15180 = FStar_Util.prefix args in
                      (match uu____15180 with
                       | (args_rhs, last_arg_rhs) ->
                           let rhs' =
                             FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                               rhs1.FStar_Syntax_Syntax.pos in
                           let uu____15250 = lhs1 in
                           (match uu____15250 with
                            | Flex (t_lhs, u_lhs, _lhs_args) ->
                                let uu____15254 =
                                  let uu____15265 =
                                    let uu____15272 =
                                      let uu____15275 =
                                        FStar_Syntax_Util.type_u () in
                                      FStar_All.pipe_left
                                        FStar_Pervasives_Native.fst
                                        uu____15275 in
                                    copy_uvar u_lhs [] uu____15272 wl1 in
                                  match uu____15265 with
                                  | (uu____15302, t_last_arg, wl2) ->
                                      let uu____15305 =
                                        let b =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg in
                                        let uu____15313 =
                                          let uu____15316 =
                                            let uu____15319 =
                                              let uu____15322 =
                                                FStar_All.pipe_right
                                                  t_res_lhs
                                                  (env1.FStar_TypeChecker_Env.universe_of
                                                     env1) in
                                              FStar_All.pipe_right
                                                uu____15322
                                                (fun uu____15325 ->
                                                   FStar_Pervasives_Native.Some
                                                     uu____15325) in
                                            FStar_All.pipe_right uu____15319
                                              (FStar_Syntax_Syntax.mk_Total'
                                                 t_res_lhs) in
                                          FStar_All.pipe_right uu____15316
                                            (FStar_Syntax_Util.arrow [b]) in
                                        copy_uvar u_lhs
                                          (FStar_List.append bs_lhs [b])
                                          uu____15313 wl2 in
                                      (match uu____15305 with
                                       | (uu____15374, lhs', wl3) ->
                                           let uu____15377 =
                                             copy_uvar u_lhs bs_lhs
                                               t_last_arg wl3 in
                                           (match uu____15377 with
                                            | (uu____15394, lhs'_last_arg,
                                               wl4) ->
                                                (lhs', lhs'_last_arg, wl4))) in
                                (match uu____15254 with
                                 | (lhs', lhs'_last_arg, wl2) ->
                                     let sol =
                                       let uu____15415 =
                                         let uu____15416 =
                                           let uu____15421 =
                                             let uu____15422 =
                                               let uu____15425 =
                                                 let uu____15426 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lhs'_last_arg in
                                                 [uu____15426] in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 lhs' uu____15425
                                                 t_lhs.FStar_Syntax_Syntax.pos in
                                             FStar_Syntax_Util.abs bs_lhs
                                               uu____15422
                                               (FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Util.residual_tot
                                                     t_res_lhs)) in
                                           (u_lhs, uu____15421) in
                                         TERM uu____15416 in
                                       [uu____15415] in
                                     let uu____15451 =
                                       let uu____15458 =
                                         mk_t_problem wl2 [] orig1 lhs'
                                           FStar_TypeChecker_Common.EQ rhs'
                                           FStar_Pervasives_Native.None
                                           "first-order lhs" in
                                       match uu____15458 with
                                       | (p1, wl3) ->
                                           let uu____15477 =
                                             mk_t_problem wl3 [] orig1
                                               lhs'_last_arg
                                               FStar_TypeChecker_Common.EQ
                                               (FStar_Pervasives_Native.fst
                                                  last_arg_rhs)
                                               FStar_Pervasives_Native.None
                                               "first-order rhs" in
                                           (match uu____15477 with
                                            | (p2, wl4) -> ([p1; p2], wl4)) in
                                     (match uu____15451 with
                                      | (sub_probs, wl3) ->
                                          let uu____15508 =
                                            let uu____15509 =
                                              solve_prob orig1
                                                FStar_Pervasives_Native.None
                                                sol wl3 in
                                            attempt sub_probs uu____15509 in
                                          solve env1 uu____15508)))) in
                let first_order orig1 env1 wl1 lhs1 rhs1 =
                  (let uu____15537 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Rel") in
                   if uu____15537
                   then FStar_Util.print_string "first_order\n"
                   else ());
                  (let is_app rhs2 =
                     let uu____15545 = FStar_Syntax_Util.head_and_args rhs2 in
                     match uu____15545 with
                     | (uu____15562, args) ->
                         (match args with | [] -> false | uu____15596 -> true) in
                   let is_arrow rhs2 =
                     let uu____15613 =
                       let uu____15614 = FStar_Syntax_Subst.compress rhs2 in
                       uu____15614.FStar_Syntax_Syntax.n in
                     match uu____15613 with
                     | FStar_Syntax_Syntax.Tm_arrow uu____15617 -> true
                     | uu____15632 -> false in
                   let uu____15633 = quasi_pattern env1 lhs1 in
                   match uu____15633 with
                   | FStar_Pervasives_Native.None ->
                       let msg =
                         mklstr
                           (fun uu____15651 ->
                              let uu____15652 = prob_to_string env1 orig1 in
                              FStar_Util.format1
                                "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                                uu____15652) in
                       giveup_or_defer env1 orig1 wl1 msg
                   | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                       let uu____15659 = is_app rhs1 in
                       if uu____15659
                       then
                         imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                           rhs1
                       else
                         (let uu____15661 = is_arrow rhs1 in
                          if uu____15661
                          then
                            imitate_arrow orig1 env1 wl1 lhs1 bs_lhs
                              t_res_lhs FStar_TypeChecker_Common.EQ rhs1
                          else
                            (let msg =
                               mklstr
                                 (fun uu____15670 ->
                                    let uu____15671 =
                                      prob_to_string env1 orig1 in
                                    FStar_Util.format1
                                      "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                      uu____15671) in
                             giveup_or_defer env1 orig1 wl1 msg))) in
                match p_rel orig with
                | FStar_TypeChecker_Common.SUB ->
                    if wl.defer_ok
                    then
                      let uu____15672 =
                        FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl uu____15672
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.SUBINV ->
                    if wl.defer_ok
                    then
                      let uu____15674 =
                        FStar_Thunk.mkv "flex-rigid subtyping" in
                      giveup_or_defer env orig wl uu____15674
                    else
                      solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs
                        rhs
                | FStar_TypeChecker_Common.EQ ->
                    let uu____15676 = lhs in
                    (match uu____15676 with
                     | Flex (_t1, ctx_uv, args_lhs) ->
                         let uu____15680 =
                           pat_vars env
                             ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                             args_lhs in
                         (match uu____15680 with
                          | FStar_Pervasives_Native.Some lhs_binders ->
                              ((let uu____15687 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel") in
                                if uu____15687
                                then
                                  FStar_Util.print_string "it's a pattern\n"
                                else ());
                               (let rhs1 = sn env rhs in
                                let names_to_string1 fvs =
                                  let uu____15700 =
                                    let uu____15703 =
                                      FStar_Util.set_elements fvs in
                                    FStar_List.map
                                      FStar_Syntax_Print.bv_to_string
                                      uu____15703 in
                                  FStar_All.pipe_right uu____15700
                                    (FStar_String.concat ", ") in
                                let fvs1 =
                                  binders_as_bv_set
                                    (FStar_List.append
                                       ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                       lhs_binders) in
                                let fvs2 = FStar_Syntax_Free.names rhs1 in
                                let uu____15720 = occurs_check ctx_uv rhs1 in
                                match uu____15720 with
                                | (uvars, occurs_ok, msg) ->
                                    if Prims.op_Negation occurs_ok
                                    then
                                      let uu____15742 =
                                        let uu____15743 =
                                          let uu____15744 =
                                            FStar_Option.get msg in
                                          Prims.op_Hat
                                            "occurs-check failed: "
                                            uu____15744 in
                                        FStar_All.pipe_left FStar_Thunk.mkv
                                          uu____15743 in
                                      giveup_or_defer env orig wl uu____15742
                                    else
                                      (let uu____15746 =
                                         FStar_Util.set_is_subset_of fvs2
                                           fvs1 in
                                       if uu____15746
                                       then
                                         let sol =
                                           mk_solution env lhs lhs_binders
                                             rhs1 in
                                         let wl1 =
                                           restrict_all_uvars env ctx_uv
                                             lhs_binders uvars wl in
                                         let uu____15751 =
                                           solve_prob orig
                                             FStar_Pervasives_Native.None sol
                                             wl1 in
                                         solve env uu____15751
                                       else
                                         if wl.defer_ok
                                         then
                                           (let msg1 =
                                              mklstr
                                                (fun uu____15764 ->
                                                   let uu____15765 =
                                                     names_to_string1 fvs2 in
                                                   let uu____15766 =
                                                     names_to_string1 fvs1 in
                                                   let uu____15767 =
                                                     FStar_Syntax_Print.binders_to_string
                                                       ", "
                                                       (FStar_List.append
                                                          ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                          lhs_binders) in
                                                   FStar_Util.format3
                                                     "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                     uu____15765 uu____15766
                                                     uu____15767) in
                                            giveup_or_defer env orig wl msg1)
                                         else
                                           first_order orig env wl lhs rhs1)))
                          | uu____15775 ->
                              if wl.defer_ok
                              then
                                let uu____15778 =
                                  FStar_Thunk.mkv "Not a pattern" in
                                giveup_or_defer env orig wl uu____15778
                              else
                                (let uu____15780 =
                                   try_quasi_pattern orig env wl lhs rhs in
                                 match uu____15780 with
                                 | (FStar_Util.Inr sol, wl1) ->
                                     let uu____15803 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None sol wl1 in
                                     solve env uu____15803
                                 | (FStar_Util.Inl msg, uu____15805) ->
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
                  let uu____15819 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15819
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok
                then
                  let uu____15821 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15821
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu____15823 =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu____15823
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
                    (let uu____15825 =
                       FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer env orig wl uu____15825)
                  else
                    (let uu____15827 =
                       let uu____15844 = quasi_pattern env lhs in
                       let uu____15851 = quasi_pattern env rhs in
                       (uu____15844, uu____15851) in
                     match uu____15827 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs, t_res_lhs),
                        FStar_Pervasives_Native.Some
                        (binders_rhs, t_res_rhs)) ->
                         let uu____15894 = lhs in
                         (match uu____15894 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____15895;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____15897;_},
                               u_lhs, uu____15899)
                              ->
                              let uu____15902 = rhs in
                              (match uu____15902 with
                               | Flex (uu____15903, u_rhs, uu____15905) ->
                                   let uu____15906 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs) in
                                   if uu____15906
                                   then
                                     let uu____15911 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl in
                                     solve env uu____15911
                                   else
                                     (let uu____15913 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                      match uu____15913 with
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
                                          let uu____15945 =
                                            let uu____15952 =
                                              let uu____15955 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs in
                                              FStar_Syntax_Util.arrow zs
                                                uu____15955 in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____15952
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
                                          (match uu____15945 with
                                           | (uu____15959, w, wl1) ->
                                               let w_app =
                                                 let uu____15963 =
                                                   FStar_List.map
                                                     (fun uu____15974 ->
                                                        match uu____15974
                                                        with
                                                        | (z, uu____15982) ->
                                                            let uu____15987 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____15987) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____15963
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____15989 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____15989
                                                 then
                                                   let uu____15990 =
                                                     let uu____15993 =
                                                       flex_t_to_string lhs in
                                                     let uu____15994 =
                                                       let uu____15997 =
                                                         flex_t_to_string rhs in
                                                       let uu____15998 =
                                                         let uu____16001 =
                                                           term_to_string w in
                                                         let uu____16002 =
                                                           let uu____16005 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____16012 =
                                                             let uu____16015
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____16022
                                                               =
                                                               let uu____16025
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____16025] in
                                                             uu____16015 ::
                                                               uu____16022 in
                                                           uu____16005 ::
                                                             uu____16012 in
                                                         uu____16001 ::
                                                           uu____16002 in
                                                       uu____15997 ::
                                                         uu____15998 in
                                                     uu____15993 ::
                                                       uu____15994 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____15990
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____16031 =
                                                       let uu____16036 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____16036) in
                                                     TERM uu____16031 in
                                                   let uu____16037 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____16037
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____16042 =
                                                          let uu____16047 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____16047) in
                                                        TERM uu____16042 in
                                                      [s1; s2]) in
                                                 let uu____16048 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____16048))))))
                     | uu____16049 ->
                         let uu____16066 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____16066)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____16115 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____16115
            then
              let uu____16116 = FStar_Syntax_Print.term_to_string t1 in
              let uu____16117 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____16118 = FStar_Syntax_Print.term_to_string t2 in
              let uu____16119 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16116 uu____16117 uu____16118 uu____16119
            else ());
           (let uu____16122 = FStar_Syntax_Util.head_and_args t1 in
            match uu____16122 with
            | (head1, args1) ->
                let uu____16165 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____16165 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16230 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____16230 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____16234 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____16234) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16252 =
                         mklstr
                           (fun uu____16263 ->
                              let uu____16264 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____16265 = args_to_string args1 in
                              let uu____16268 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____16269 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____16264 uu____16265 uu____16268
                                uu____16269) in
                       giveup env1 uu____16252 orig
                     else
                       (let uu____16273 =
                          (nargs = Prims.int_zero) ||
                            (let uu____16275 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____16275 = FStar_Syntax_Util.Equal) in
                        if uu____16273
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2638_16277 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2638_16277.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2638_16277.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2638_16277.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2638_16277.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2638_16277.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2638_16277.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2638_16277.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2638_16277.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____16284 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____16284
                                    else solve env1 wl2))
                        else
                          (let uu____16287 = base_and_refinement env1 t1 in
                           match uu____16287 with
                           | (base1, refinement1) ->
                               let uu____16312 = base_and_refinement env1 t2 in
                               (match uu____16312 with
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
                                           let uu____16475 =
                                             FStar_List.fold_right
                                               (fun uu____16515 ->
                                                  fun uu____16516 ->
                                                    match (uu____16515,
                                                            uu____16516)
                                                    with
                                                    | (((a1, uu____16568),
                                                        (a2, uu____16570)),
                                                       (probs, wl3)) ->
                                                        let uu____16619 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____16619
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____16475 with
                                           | (subprobs, wl3) ->
                                               ((let uu____16661 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16661
                                                 then
                                                   let uu____16662 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____16662
                                                 else ());
                                                (let uu____16665 =
                                                   FStar_Options.defensive () in
                                                 if uu____16665
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
                                                    (let uu____16685 =
                                                       mk_sub_probs wl3 in
                                                     match uu____16685 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____16701 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____16701 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____16709 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____16709)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____16733 =
                                                    mk_sub_probs wl3 in
                                                  match uu____16733 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____16749 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____16749 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____16757 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____16757) in
                                         let unfold_and_retry d env2 wl2
                                           uu____16784 =
                                           match uu____16784 with
                                           | (prob, reason) ->
                                               ((let uu____16798 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16798
                                                 then
                                                   let uu____16799 =
                                                     prob_to_string env2 orig in
                                                   let uu____16800 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____16799 uu____16800
                                                 else ());
                                                (let uu____16802 =
                                                   let uu____16811 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____16814 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____16811, uu____16814) in
                                                 match uu____16802 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____16827 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____16827 with
                                                      | (head1', uu____16845)
                                                          ->
                                                          let uu____16870 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____16870
                                                           with
                                                           | (head2',
                                                              uu____16888) ->
                                                               let uu____16913
                                                                 =
                                                                 let uu____16918
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____16919
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____16918,
                                                                   uu____16919) in
                                                               (match uu____16913
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu____16921
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____16921
                                                                    then
                                                                    let uu____16922
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____16923
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____16924
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____16925
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____16922
                                                                    uu____16923
                                                                    uu____16924
                                                                    uu____16925
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____16927
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2726_16935
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2726_16935.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2726_16935.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2726_16935.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2726_16935.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2726_16935.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2726_16935.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2726_16935.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2726_16935.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
                                                                    let uu____16937
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____16937
                                                                    then
                                                                    let uu____16938
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____16938
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____16940 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____16952 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____16952 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____16959 =
                                             let uu____16960 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____16960.FStar_Syntax_Syntax.n in
                                           match uu____16959 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____16964 -> false in
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
                                          | uu____16966 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____16969 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2746_17005 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2746_17005.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2746_17005.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2746_17005.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2746_17005.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2746_17005.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2746_17005.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2746_17005.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2746_17005.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____17080 = destruct_flex_t scrutinee wl1 in
             match uu____17080 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____17091 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____17091 with
                  | (xs, pat_term, uu____17106, uu____17107) ->
                      let uu____17112 =
                        FStar_List.fold_left
                          (fun uu____17135 ->
                             fun x ->
                               match uu____17135 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____17156 = copy_uvar uv [] t_x wl3 in
                                   (match uu____17156 with
                                    | (uu____17175, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____17112 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____17196 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____17196 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2787_17212 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2787_17212.wl_deferred_to_tac);
                                    ctr = (uu___2787_17212.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2787_17212.umax_heuristic_ok);
                                    tcenv = (uu___2787_17212.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2787_17212.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____17220 = solve env1 wl' in
                                (match uu____17220 with
                                 | Success (uu____17223, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2796_17227 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2796_17227.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2796_17227.wl_deferred_to_tac);
                                         ctr = (uu___2796_17227.ctr);
                                         defer_ok =
                                           (uu___2796_17227.defer_ok);
                                         smt_ok = (uu___2796_17227.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2796_17227.umax_heuristic_ok);
                                         tcenv = (uu___2796_17227.tcenv);
                                         wl_implicits =
                                           (uu___2796_17227.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2796_17227.repr_subcomp_allowed)
                                       } in
                                     let uu____17228 = solve env1 wl'1 in
                                     (match uu____17228 with
                                      | Success
                                          (uu____17231, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____17235 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____17235))
                                      | Failed uu____17240 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17246 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____17267 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____17267
                 then
                   let uu____17268 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____17269 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17268 uu____17269
                 else ());
                (let uu____17271 =
                   let uu____17292 =
                     let uu____17301 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____17301) in
                   let uu____17308 =
                     let uu____17317 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____17317) in
                   (uu____17292, uu____17308) in
                 match uu____17271 with
                 | ((uu____17346,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____17349;
                       FStar_Syntax_Syntax.vars = uu____17350;_}),
                    (s, t)) ->
                     let uu____17421 =
                       let uu____17422 = is_flex scrutinee in
                       Prims.op_Negation uu____17422 in
                     if uu____17421
                     then
                       ((let uu____17430 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____17430
                         then
                           let uu____17431 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17431
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17443 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17443
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17449 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17449
                           then
                             let uu____17450 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____17451 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17450 uu____17451
                           else ());
                          (let pat_discriminates uu___26_17472 =
                             match uu___26_17472 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17487;
                                  FStar_Syntax_Syntax.p = uu____17488;_},
                                FStar_Pervasives_Native.None, uu____17489) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17502;
                                  FStar_Syntax_Syntax.p = uu____17503;_},
                                FStar_Pervasives_Native.None, uu____17504) ->
                                 true
                             | uu____17529 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____17629 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____17629 with
                                       | (uu____17630, uu____17631, t') ->
                                           let uu____17649 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____17649 with
                                            | (FullMatch, uu____17660) ->
                                                true
                                            | (HeadMatch uu____17673,
                                               uu____17674) -> true
                                            | uu____17687 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____17720 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____17720
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17725 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____17725 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____17813, uu____17814)
                                       -> branches1
                                   | uu____17959 -> branches in
                                 let uu____18014 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____18023 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____18023 with
                                        | (p, uu____18027, uu____18028) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____18055 ->
                                      FStar_Util.Inr uu____18055) uu____18014))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18085 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____18085 with
                                | (p, uu____18093, e) ->
                                    ((let uu____18112 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____18112
                                      then
                                        let uu____18113 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____18114 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18113 uu____18114
                                      else ());
                                     (let uu____18116 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____18129 ->
                                           FStar_Util.Inr uu____18129)
                                        uu____18116)))))
                 | ((s, t),
                    (uu____18132,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____18135;
                       FStar_Syntax_Syntax.vars = uu____18136;_}))
                     ->
                     let uu____18205 =
                       let uu____18206 = is_flex scrutinee in
                       Prims.op_Negation uu____18206 in
                     if uu____18205
                     then
                       ((let uu____18214 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____18214
                         then
                           let uu____18215 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18215
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18227 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18227
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18233 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18233
                           then
                             let uu____18234 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____18235 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18234 uu____18235
                           else ());
                          (let pat_discriminates uu___26_18256 =
                             match uu___26_18256 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18271;
                                  FStar_Syntax_Syntax.p = uu____18272;_},
                                FStar_Pervasives_Native.None, uu____18273) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18286;
                                  FStar_Syntax_Syntax.p = uu____18287;_},
                                FStar_Pervasives_Native.None, uu____18288) ->
                                 true
                             | uu____18313 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____18413 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____18413 with
                                       | (uu____18414, uu____18415, t') ->
                                           let uu____18433 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____18433 with
                                            | (FullMatch, uu____18444) ->
                                                true
                                            | (HeadMatch uu____18457,
                                               uu____18458) -> true
                                            | uu____18471 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____18504 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____18504
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18509 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____18509 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____18597, uu____18598)
                                       -> branches1
                                   | uu____18743 -> branches in
                                 let uu____18798 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____18807 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____18807 with
                                        | (p, uu____18811, uu____18812) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____18839 ->
                                      FStar_Util.Inr uu____18839) uu____18798))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18869 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____18869 with
                                | (p, uu____18877, e) ->
                                    ((let uu____18896 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____18896
                                      then
                                        let uu____18897 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____18898 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18897 uu____18898
                                      else ());
                                     (let uu____18900 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____18913 ->
                                           FStar_Util.Inr uu____18913)
                                        uu____18900)))))
                 | uu____18914 ->
                     ((let uu____18936 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____18936
                       then
                         let uu____18937 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____18938 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____18937 uu____18938
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____18980 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____18980
            then
              let uu____18981 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____18982 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____18983 = FStar_Syntax_Print.term_to_string t1 in
              let uu____18984 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____18981 uu____18982 uu____18983 uu____18984
            else ());
           (let uu____18986 = head_matches_delta env1 wl1 t1 t2 in
            match uu____18986 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____19017, uu____19018) ->
                     let rec may_relate head =
                       let uu____19045 =
                         let uu____19046 = FStar_Syntax_Subst.compress head in
                         uu____19046.FStar_Syntax_Syntax.n in
                       match uu____19045 with
                       | FStar_Syntax_Syntax.Tm_name uu____19049 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____19050 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____19074 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____19074 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____19075 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____19076
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____19077 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____19079, uu____19080) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____19122) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____19128) ->
                           may_relate t
                       | uu____19133 -> false in
                     let uu____19134 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____19134 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____19144 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____19144
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____19150 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____19150
                          then
                            let uu____19151 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____19151 with
                             | (guard, wl2) ->
                                 let uu____19158 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____19158)
                          else
                            (let uu____19160 =
                               mklstr
                                 (fun uu____19171 ->
                                    let uu____19172 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____19173 =
                                      let uu____19174 =
                                        let uu____19177 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____19177
                                          (fun x ->
                                             let uu____19183 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____19183) in
                                      FStar_Util.dflt "" uu____19174 in
                                    let uu____19184 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____19185 =
                                      let uu____19186 =
                                        let uu____19189 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____19189
                                          (fun x ->
                                             let uu____19195 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____19195) in
                                      FStar_Util.dflt "" uu____19186 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____19172 uu____19173 uu____19184
                                      uu____19185) in
                             giveup env1 uu____19160 orig))
                 | (HeadMatch (true), uu____19196) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____19209 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____19209 with
                        | (guard, wl2) ->
                            let uu____19216 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____19216)
                     else
                       (let uu____19218 =
                          mklstr
                            (fun uu____19225 ->
                               let uu____19226 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____19227 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____19226 uu____19227) in
                        giveup env1 uu____19218 orig)
                 | (uu____19228, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2978_19242 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2978_19242.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2978_19242.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2978_19242.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2978_19242.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2978_19242.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2978_19242.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2978_19242.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2978_19242.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____19266 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____19266
          then
            let uu____19267 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____19267
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____19272 =
                let uu____19275 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19275 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____19272 t1);
             (let uu____19293 =
                let uu____19296 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19296 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____19293 t2);
             (let uu____19314 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____19314
              then
                let uu____19315 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____19316 =
                  let uu____19317 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____19318 =
                    let uu____19319 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____19319 in
                  Prims.op_Hat uu____19317 uu____19318 in
                let uu____19320 =
                  let uu____19321 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____19322 =
                    let uu____19323 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____19323 in
                  Prims.op_Hat uu____19321 uu____19322 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____19315 uu____19316 uu____19320
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____19326, uu____19327) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____19342, FStar_Syntax_Syntax.Tm_delayed uu____19343) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____19358, uu____19359) ->
                  let uu____19386 =
                    let uu___3009_19387 = problem in
                    let uu____19388 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3009_19387.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19388;
                      FStar_TypeChecker_Common.relation =
                        (uu___3009_19387.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3009_19387.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3009_19387.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3009_19387.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3009_19387.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3009_19387.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3009_19387.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3009_19387.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19386 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____19389, uu____19390) ->
                  let uu____19397 =
                    let uu___3015_19398 = problem in
                    let uu____19399 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3015_19398.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19399;
                      FStar_TypeChecker_Common.relation =
                        (uu___3015_19398.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___3015_19398.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___3015_19398.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3015_19398.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3015_19398.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3015_19398.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3015_19398.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3015_19398.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19397 wl
              | (uu____19400, FStar_Syntax_Syntax.Tm_ascribed uu____19401) ->
                  let uu____19428 =
                    let uu___3021_19429 = problem in
                    let uu____19430 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3021_19429.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3021_19429.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3021_19429.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19430;
                      FStar_TypeChecker_Common.element =
                        (uu___3021_19429.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3021_19429.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3021_19429.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3021_19429.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3021_19429.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3021_19429.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19428 wl
              | (uu____19431, FStar_Syntax_Syntax.Tm_meta uu____19432) ->
                  let uu____19439 =
                    let uu___3027_19440 = problem in
                    let uu____19441 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3027_19440.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3027_19440.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3027_19440.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19441;
                      FStar_TypeChecker_Common.element =
                        (uu___3027_19440.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3027_19440.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3027_19440.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3027_19440.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3027_19440.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3027_19440.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19439 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____19443),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____19445)) ->
                  let uu____19454 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____19454
              | (FStar_Syntax_Syntax.Tm_bvar uu____19455, uu____19456) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____19457, FStar_Syntax_Syntax.Tm_bvar uu____19458) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_19527 =
                    match uu___27_19527 with
                    | [] -> c
                    | bs ->
                        let uu____19555 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____19555 in
                  let uu____19566 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____19566 with
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
                                    let uu____19715 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____19715
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_19800 =
                    match uu___28_19800 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____19842 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____19842 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____19987 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____19988 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____19987
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____19988 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____19989, uu____19990) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20019 -> true
                    | uu____20038 -> false in
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
                      (let uu____20091 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3129_20099 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3129_20099.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3129_20099.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3129_20099.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3129_20099.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3129_20099.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3129_20099.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3129_20099.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3129_20099.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3129_20099.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3129_20099.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3129_20099.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3129_20099.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3129_20099.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3129_20099.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3129_20099.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3129_20099.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3129_20099.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3129_20099.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3129_20099.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3129_20099.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3129_20099.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3129_20099.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3129_20099.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3129_20099.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3129_20099.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3129_20099.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3129_20099.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3129_20099.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3129_20099.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3129_20099.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3129_20099.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3129_20099.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3129_20099.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3129_20099.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3129_20099.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3129_20099.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3129_20099.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3129_20099.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3129_20099.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3129_20099.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3129_20099.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3129_20099.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3129_20099.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3129_20099.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____20091 with
                       | (uu____20102, ty, uu____20104) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____20113 =
                                 let uu____20114 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____20114.FStar_Syntax_Syntax.n in
                               match uu____20113 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20117 ->
                                   let uu____20124 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____20124
                               | uu____20125 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____20128 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____20128
                             then
                               let uu____20129 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____20130 =
                                 let uu____20131 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20131 in
                               let uu____20132 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20129 uu____20130 uu____20132
                             else ());
                            r1)) in
                  let uu____20134 =
                    let uu____20151 = maybe_eta t1 in
                    let uu____20158 = maybe_eta t2 in
                    (uu____20151, uu____20158) in
                  (match uu____20134 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3150_20200 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3150_20200.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3150_20200.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3150_20200.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3150_20200.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3150_20200.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3150_20200.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3150_20200.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3150_20200.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20221 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20221
                       then
                         let uu____20222 = destruct_flex_t not_abs wl in
                         (match uu____20222 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3167_20237 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3167_20237.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3167_20237.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3167_20237.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3167_20237.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3167_20237.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3167_20237.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3167_20237.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3167_20237.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20239 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20239 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20260 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20260
                       then
                         let uu____20261 = destruct_flex_t not_abs wl in
                         (match uu____20261 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3167_20276 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3167_20276.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3167_20276.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3167_20276.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3167_20276.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3167_20276.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3167_20276.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3167_20276.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3167_20276.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20278 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20278 orig))
                   | uu____20279 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____20296, FStar_Syntax_Syntax.Tm_abs uu____20297) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20326 -> true
                    | uu____20345 -> false in
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
                      (let uu____20398 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3129_20406 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3129_20406.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3129_20406.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3129_20406.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3129_20406.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3129_20406.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3129_20406.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3129_20406.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3129_20406.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3129_20406.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3129_20406.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3129_20406.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3129_20406.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3129_20406.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3129_20406.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3129_20406.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3129_20406.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3129_20406.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3129_20406.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3129_20406.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3129_20406.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3129_20406.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3129_20406.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3129_20406.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3129_20406.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3129_20406.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3129_20406.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3129_20406.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3129_20406.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3129_20406.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3129_20406.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3129_20406.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3129_20406.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3129_20406.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3129_20406.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3129_20406.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3129_20406.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3129_20406.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3129_20406.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3129_20406.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3129_20406.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3129_20406.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3129_20406.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3129_20406.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3129_20406.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____20398 with
                       | (uu____20409, ty, uu____20411) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____20420 =
                                 let uu____20421 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____20421.FStar_Syntax_Syntax.n in
                               match uu____20420 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20424 ->
                                   let uu____20431 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____20431
                               | uu____20432 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____20435 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____20435
                             then
                               let uu____20436 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____20437 =
                                 let uu____20438 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20438 in
                               let uu____20439 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20436 uu____20437 uu____20439
                             else ());
                            r1)) in
                  let uu____20441 =
                    let uu____20458 = maybe_eta t1 in
                    let uu____20465 = maybe_eta t2 in
                    (uu____20458, uu____20465) in
                  (match uu____20441 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3150_20507 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3150_20507.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3150_20507.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3150_20507.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3150_20507.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3150_20507.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3150_20507.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3150_20507.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3150_20507.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20528 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20528
                       then
                         let uu____20529 = destruct_flex_t not_abs wl in
                         (match uu____20529 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3167_20544 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3167_20544.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3167_20544.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3167_20544.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3167_20544.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3167_20544.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3167_20544.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3167_20544.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3167_20544.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20546 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20546 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20567 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20567
                       then
                         let uu____20568 = destruct_flex_t not_abs wl in
                         (match uu____20568 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3167_20583 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3167_20583.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3167_20583.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3167_20583.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3167_20583.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3167_20583.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3167_20583.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3167_20583.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3167_20583.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20585 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20585 orig))
                   | uu____20586 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____20615 =
                    let uu____20620 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____20620 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3190_20648 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3190_20648.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3190_20648.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3192_20650 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3192_20650.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3192_20650.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____20651, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3190_20665 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3190_20665.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3190_20665.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3192_20667 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3192_20667.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3192_20667.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____20668 -> (x1, x2) in
                  (match uu____20615 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____20687 = as_refinement false env t11 in
                       (match uu____20687 with
                        | (x12, phi11) ->
                            let uu____20694 = as_refinement false env t21 in
                            (match uu____20694 with
                             | (x22, phi21) ->
                                 ((let uu____20702 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____20702
                                   then
                                     ((let uu____20704 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____20705 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____20706 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____20704
                                         uu____20705 uu____20706);
                                      (let uu____20707 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____20708 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____20709 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____20707
                                         uu____20708 uu____20709))
                                   else ());
                                  (let uu____20711 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____20711 with
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
                                         let uu____20779 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____20779
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____20791 =
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
                                         (let uu____20802 =
                                            let uu____20805 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20805 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____20802
                                            (p_guard base_prob));
                                         (let uu____20823 =
                                            let uu____20826 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20826 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____20823
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____20844 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____20844) in
                                       let has_uvars =
                                         (let uu____20848 =
                                            let uu____20849 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____20849 in
                                          Prims.op_Negation uu____20848) ||
                                           (let uu____20853 =
                                              let uu____20854 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____20854 in
                                            Prims.op_Negation uu____20853) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____20857 =
                                           let uu____20862 =
                                             let uu____20871 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____20871] in
                                           mk_t_problem wl1 uu____20862 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____20857 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____20893 =
                                                solve env1
                                                  (let uu___3235_20895 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3235_20895.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3235_20895.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3235_20895.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3235_20895.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3235_20895.tcenv);
                                                     wl_implicits =
                                                       (uu___3235_20895.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3235_20895.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____20893 with
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
                                                   (uu____20906,
                                                    defer_to_tac,
                                                    uu____20908)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____20913 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____20913 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3251_20922 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3251_20922.attempting);
                                                         wl_deferred =
                                                           (uu___3251_20922.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3251_20922.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3251_20922.defer_ok);
                                                         smt_ok =
                                                           (uu___3251_20922.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3251_20922.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3251_20922.tcenv);
                                                         wl_implicits =
                                                           (uu___3251_20922.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3251_20922.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____20924 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____20924))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20926,
                 FStar_Syntax_Syntax.Tm_uvar uu____20927) ->
                  let uu____20952 = ensure_no_uvar_subst t1 wl in
                  (match uu____20952 with
                   | (t11, wl1) ->
                       let uu____20959 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20959 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20968;
                    FStar_Syntax_Syntax.pos = uu____20969;
                    FStar_Syntax_Syntax.vars = uu____20970;_},
                  uu____20971),
                 FStar_Syntax_Syntax.Tm_uvar uu____20972) ->
                  let uu____21021 = ensure_no_uvar_subst t1 wl in
                  (match uu____21021 with
                   | (t11, wl1) ->
                       let uu____21028 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21028 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____21037,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21038;
                    FStar_Syntax_Syntax.pos = uu____21039;
                    FStar_Syntax_Syntax.vars = uu____21040;_},
                  uu____21041)) ->
                  let uu____21090 = ensure_no_uvar_subst t1 wl in
                  (match uu____21090 with
                   | (t11, wl1) ->
                       let uu____21097 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21097 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21106;
                    FStar_Syntax_Syntax.pos = uu____21107;
                    FStar_Syntax_Syntax.vars = uu____21108;_},
                  uu____21109),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21110;
                    FStar_Syntax_Syntax.pos = uu____21111;
                    FStar_Syntax_Syntax.vars = uu____21112;_},
                  uu____21113)) ->
                  let uu____21186 = ensure_no_uvar_subst t1 wl in
                  (match uu____21186 with
                   | (t11, wl1) ->
                       let uu____21193 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____21193 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____21202, uu____21203) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21216 = destruct_flex_t t1 wl in
                  (match uu____21216 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21223;
                    FStar_Syntax_Syntax.pos = uu____21224;
                    FStar_Syntax_Syntax.vars = uu____21225;_},
                  uu____21226),
                 uu____21227) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21264 = destruct_flex_t t1 wl in
                  (match uu____21264 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____21271, FStar_Syntax_Syntax.Tm_uvar uu____21272) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____21285, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21286;
                    FStar_Syntax_Syntax.pos = uu____21287;
                    FStar_Syntax_Syntax.vars = uu____21288;_},
                  uu____21289)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____21326,
                 FStar_Syntax_Syntax.Tm_arrow uu____21327) ->
                  solve_t' env
                    (let uu___3354_21355 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3354_21355.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3354_21355.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3354_21355.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3354_21355.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3354_21355.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3354_21355.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3354_21355.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3354_21355.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3354_21355.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21356;
                    FStar_Syntax_Syntax.pos = uu____21357;
                    FStar_Syntax_Syntax.vars = uu____21358;_},
                  uu____21359),
                 FStar_Syntax_Syntax.Tm_arrow uu____21360) ->
                  solve_t' env
                    (let uu___3354_21412 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3354_21412.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3354_21412.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3354_21412.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3354_21412.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3354_21412.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3354_21412.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3354_21412.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3354_21412.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3354_21412.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21413, FStar_Syntax_Syntax.Tm_uvar uu____21414) ->
                  let uu____21427 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21427
              | (uu____21428, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21429;
                    FStar_Syntax_Syntax.pos = uu____21430;
                    FStar_Syntax_Syntax.vars = uu____21431;_},
                  uu____21432)) ->
                  let uu____21469 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21469
              | (FStar_Syntax_Syntax.Tm_uvar uu____21470, uu____21471) ->
                  let uu____21484 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21484
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21485;
                    FStar_Syntax_Syntax.pos = uu____21486;
                    FStar_Syntax_Syntax.vars = uu____21487;_},
                  uu____21488),
                 uu____21489) ->
                  let uu____21526 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21526
              | (FStar_Syntax_Syntax.Tm_refine uu____21527, uu____21528) ->
                  let t21 =
                    let uu____21536 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____21536 in
                  solve_t env
                    (let uu___3389_21562 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3389_21562.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3389_21562.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3389_21562.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3389_21562.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3389_21562.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3389_21562.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3389_21562.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3389_21562.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3389_21562.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21563, FStar_Syntax_Syntax.Tm_refine uu____21564) ->
                  let t11 =
                    let uu____21572 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____21572 in
                  solve_t env
                    (let uu___3396_21598 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3396_21598.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3396_21598.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3396_21598.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3396_21598.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3396_21598.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3396_21598.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3396_21598.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3396_21598.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3396_21598.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____21680 =
                    let uu____21681 = guard_of_prob env wl problem t1 t2 in
                    match uu____21681 with
                    | (guard, wl1) ->
                        let uu____21688 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____21688 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____21907 = br1 in
                        (match uu____21907 with
                         | (p1, w1, uu____21936) ->
                             let uu____21953 = br2 in
                             (match uu____21953 with
                              | (p2, w2, uu____21976) ->
                                  let uu____21981 =
                                    let uu____21982 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____21982 in
                                  if uu____21981
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____22006 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____22006 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____22043 = br2 in
                                         (match uu____22043 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____22076 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____22076 in
                                              let uu____22081 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____22112,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____22133) ->
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
                                                    let uu____22192 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____22192 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____22081
                                                (fun uu____22263 ->
                                                   match uu____22263 with
                                                   | (wprobs, wl2) ->
                                                       let uu____22300 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____22300
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____22320
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____22320
                                                              then
                                                                let uu____22321
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____22322
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____22321
                                                                  uu____22322
                                                              else ());
                                                             (let uu____22324
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____22324
                                                                (fun
                                                                   uu____22360
                                                                   ->
                                                                   match uu____22360
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
                    | uu____22489 -> FStar_Pervasives_Native.None in
                  let uu____22530 = solve_branches wl brs1 brs2 in
                  (match uu____22530 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____22554 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____22554 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____22579 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____22579 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____22612 =
                                FStar_List.map
                                  (fun uu____22624 ->
                                     match uu____22624 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____22612 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____22633 =
                              let uu____22634 =
                                let uu____22635 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____22635
                                  (let uu___3495_22643 = wl3 in
                                   {
                                     attempting =
                                       (uu___3495_22643.attempting);
                                     wl_deferred =
                                       (uu___3495_22643.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3495_22643.wl_deferred_to_tac);
                                     ctr = (uu___3495_22643.ctr);
                                     defer_ok = (uu___3495_22643.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3495_22643.umax_heuristic_ok);
                                     tcenv = (uu___3495_22643.tcenv);
                                     wl_implicits =
                                       (uu___3495_22643.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3495_22643.repr_subcomp_allowed)
                                   }) in
                              solve env uu____22634 in
                            (match uu____22633 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____22648 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____22655 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____22655 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____22656, uu____22657) ->
                  let head1 =
                    let uu____22681 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22681
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22727 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22727
                      FStar_Pervasives_Native.fst in
                  ((let uu____22773 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22773
                    then
                      let uu____22774 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22775 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22776 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22774 uu____22775 uu____22776
                    else ());
                   (let no_free_uvars t =
                      (let uu____22786 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22786) &&
                        (let uu____22790 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22790) in
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
                      let uu____22806 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22806 = FStar_Syntax_Util.Equal in
                    let uu____22807 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22807
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22808 = equal t1 t2 in
                         (if uu____22808
                          then
                            let uu____22809 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22809
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22812 =
                            let uu____22819 = equal t1 t2 in
                            if uu____22819
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22829 = mk_eq2 wl env orig t1 t2 in
                               match uu____22829 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22812 with
                          | (guard, wl1) ->
                              let uu____22850 = solve_prob orig guard [] wl1 in
                              solve env uu____22850))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____22852, uu____22853) ->
                  let head1 =
                    let uu____22861 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22861
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22907 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22907
                      FStar_Pervasives_Native.fst in
                  ((let uu____22953 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22953
                    then
                      let uu____22954 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22955 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22956 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22954 uu____22955 uu____22956
                    else ());
                   (let no_free_uvars t =
                      (let uu____22966 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22966) &&
                        (let uu____22970 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22970) in
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
                      let uu____22986 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22986 = FStar_Syntax_Util.Equal in
                    let uu____22987 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22987
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22988 = equal t1 t2 in
                         (if uu____22988
                          then
                            let uu____22989 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22989
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22992 =
                            let uu____22999 = equal t1 t2 in
                            if uu____22999
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23009 = mk_eq2 wl env orig t1 t2 in
                               match uu____23009 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22992 with
                          | (guard, wl1) ->
                              let uu____23030 = solve_prob orig guard [] wl1 in
                              solve env uu____23030))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____23032, uu____23033) ->
                  let head1 =
                    let uu____23035 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23035
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23081 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23081
                      FStar_Pervasives_Native.fst in
                  ((let uu____23127 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23127
                    then
                      let uu____23128 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23129 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23130 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23128 uu____23129 uu____23130
                    else ());
                   (let no_free_uvars t =
                      (let uu____23140 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23140) &&
                        (let uu____23144 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23144) in
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
                      let uu____23160 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23160 = FStar_Syntax_Util.Equal in
                    let uu____23161 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23161
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23162 = equal t1 t2 in
                         (if uu____23162
                          then
                            let uu____23163 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23163
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23166 =
                            let uu____23173 = equal t1 t2 in
                            if uu____23173
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23183 = mk_eq2 wl env orig t1 t2 in
                               match uu____23183 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23166 with
                          | (guard, wl1) ->
                              let uu____23204 = solve_prob orig guard [] wl1 in
                              solve env uu____23204))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____23206, uu____23207) ->
                  let head1 =
                    let uu____23209 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23209
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23255 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23255
                      FStar_Pervasives_Native.fst in
                  ((let uu____23301 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23301
                    then
                      let uu____23302 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23303 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23304 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23302 uu____23303 uu____23304
                    else ());
                   (let no_free_uvars t =
                      (let uu____23314 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23314) &&
                        (let uu____23318 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23318) in
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
                      let uu____23334 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23334 = FStar_Syntax_Util.Equal in
                    let uu____23335 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23335
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23336 = equal t1 t2 in
                         (if uu____23336
                          then
                            let uu____23337 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23337
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23340 =
                            let uu____23347 = equal t1 t2 in
                            if uu____23347
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23357 = mk_eq2 wl env orig t1 t2 in
                               match uu____23357 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23340 with
                          | (guard, wl1) ->
                              let uu____23378 = solve_prob orig guard [] wl1 in
                              solve env uu____23378))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____23380, uu____23381) ->
                  let head1 =
                    let uu____23383 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23383
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23423 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23423
                      FStar_Pervasives_Native.fst in
                  ((let uu____23463 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23463
                    then
                      let uu____23464 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23465 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23466 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23464 uu____23465 uu____23466
                    else ());
                   (let no_free_uvars t =
                      (let uu____23476 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23476) &&
                        (let uu____23480 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23480) in
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
                      let uu____23496 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23496 = FStar_Syntax_Util.Equal in
                    let uu____23497 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23497
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23498 = equal t1 t2 in
                         (if uu____23498
                          then
                            let uu____23499 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23499
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23502 =
                            let uu____23509 = equal t1 t2 in
                            if uu____23509
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23519 = mk_eq2 wl env orig t1 t2 in
                               match uu____23519 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23502 with
                          | (guard, wl1) ->
                              let uu____23540 = solve_prob orig guard [] wl1 in
                              solve env uu____23540))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____23542, uu____23543) ->
                  let head1 =
                    let uu____23561 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23561
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23601 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23601
                      FStar_Pervasives_Native.fst in
                  ((let uu____23641 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23641
                    then
                      let uu____23642 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23643 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23644 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23642 uu____23643 uu____23644
                    else ());
                   (let no_free_uvars t =
                      (let uu____23654 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23654) &&
                        (let uu____23658 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23658) in
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
                      let uu____23674 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23674 = FStar_Syntax_Util.Equal in
                    let uu____23675 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23675
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23676 = equal t1 t2 in
                         (if uu____23676
                          then
                            let uu____23677 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23677
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23680 =
                            let uu____23687 = equal t1 t2 in
                            if uu____23687
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23697 = mk_eq2 wl env orig t1 t2 in
                               match uu____23697 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23680 with
                          | (guard, wl1) ->
                              let uu____23718 = solve_prob orig guard [] wl1 in
                              solve env uu____23718))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23720, FStar_Syntax_Syntax.Tm_match uu____23721) ->
                  let head1 =
                    let uu____23745 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23745
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23785 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23785
                      FStar_Pervasives_Native.fst in
                  ((let uu____23825 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23825
                    then
                      let uu____23826 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23827 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23828 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23826 uu____23827 uu____23828
                    else ());
                   (let no_free_uvars t =
                      (let uu____23838 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23838) &&
                        (let uu____23842 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23842) in
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
                      let uu____23858 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23858 = FStar_Syntax_Util.Equal in
                    let uu____23859 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23859
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23860 = equal t1 t2 in
                         (if uu____23860
                          then
                            let uu____23861 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23861
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23864 =
                            let uu____23871 = equal t1 t2 in
                            if uu____23871
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23881 = mk_eq2 wl env orig t1 t2 in
                               match uu____23881 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23864 with
                          | (guard, wl1) ->
                              let uu____23902 = solve_prob orig guard [] wl1 in
                              solve env uu____23902))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23904, FStar_Syntax_Syntax.Tm_uinst uu____23905) ->
                  let head1 =
                    let uu____23913 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23913
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23953 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23953
                      FStar_Pervasives_Native.fst in
                  ((let uu____23993 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23993
                    then
                      let uu____23994 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23995 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23996 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23994 uu____23995 uu____23996
                    else ());
                   (let no_free_uvars t =
                      (let uu____24006 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24006) &&
                        (let uu____24010 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24010) in
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
                      let uu____24026 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24026 = FStar_Syntax_Util.Equal in
                    let uu____24027 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24027
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24028 = equal t1 t2 in
                         (if uu____24028
                          then
                            let uu____24029 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24029
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24032 =
                            let uu____24039 = equal t1 t2 in
                            if uu____24039
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24049 = mk_eq2 wl env orig t1 t2 in
                               match uu____24049 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24032 with
                          | (guard, wl1) ->
                              let uu____24070 = solve_prob orig guard [] wl1 in
                              solve env uu____24070))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24072, FStar_Syntax_Syntax.Tm_name uu____24073) ->
                  let head1 =
                    let uu____24075 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24075
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24115 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24115
                      FStar_Pervasives_Native.fst in
                  ((let uu____24155 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24155
                    then
                      let uu____24156 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24157 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24158 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24156 uu____24157 uu____24158
                    else ());
                   (let no_free_uvars t =
                      (let uu____24168 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24168) &&
                        (let uu____24172 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24172) in
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
                      let uu____24188 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24188 = FStar_Syntax_Util.Equal in
                    let uu____24189 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24189
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24190 = equal t1 t2 in
                         (if uu____24190
                          then
                            let uu____24191 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24191
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24194 =
                            let uu____24201 = equal t1 t2 in
                            if uu____24201
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24211 = mk_eq2 wl env orig t1 t2 in
                               match uu____24211 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24194 with
                          | (guard, wl1) ->
                              let uu____24232 = solve_prob orig guard [] wl1 in
                              solve env uu____24232))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24234, FStar_Syntax_Syntax.Tm_constant uu____24235) ->
                  let head1 =
                    let uu____24237 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24237
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24277 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24277
                      FStar_Pervasives_Native.fst in
                  ((let uu____24317 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24317
                    then
                      let uu____24318 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24319 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24320 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24318 uu____24319 uu____24320
                    else ());
                   (let no_free_uvars t =
                      (let uu____24330 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24330) &&
                        (let uu____24334 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24334) in
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
                      let uu____24350 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24350 = FStar_Syntax_Util.Equal in
                    let uu____24351 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24351
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24352 = equal t1 t2 in
                         (if uu____24352
                          then
                            let uu____24353 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24353
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24356 =
                            let uu____24363 = equal t1 t2 in
                            if uu____24363
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24373 = mk_eq2 wl env orig t1 t2 in
                               match uu____24373 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24356 with
                          | (guard, wl1) ->
                              let uu____24394 = solve_prob orig guard [] wl1 in
                              solve env uu____24394))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24396, FStar_Syntax_Syntax.Tm_fvar uu____24397) ->
                  let head1 =
                    let uu____24399 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24399
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24445 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24445
                      FStar_Pervasives_Native.fst in
                  ((let uu____24491 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24491
                    then
                      let uu____24492 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24493 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24494 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24492 uu____24493 uu____24494
                    else ());
                   (let no_free_uvars t =
                      (let uu____24504 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24504) &&
                        (let uu____24508 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24508) in
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
                      let uu____24524 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24524 = FStar_Syntax_Util.Equal in
                    let uu____24525 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24525
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24526 = equal t1 t2 in
                         (if uu____24526
                          then
                            let uu____24527 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24527
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24530 =
                            let uu____24537 = equal t1 t2 in
                            if uu____24537
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24547 = mk_eq2 wl env orig t1 t2 in
                               match uu____24547 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24530 with
                          | (guard, wl1) ->
                              let uu____24568 = solve_prob orig guard [] wl1 in
                              solve env uu____24568))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24570, FStar_Syntax_Syntax.Tm_app uu____24571) ->
                  let head1 =
                    let uu____24589 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24589
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24629 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24629
                      FStar_Pervasives_Native.fst in
                  ((let uu____24669 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24669
                    then
                      let uu____24670 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24671 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24672 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24670 uu____24671 uu____24672
                    else ());
                   (let no_free_uvars t =
                      (let uu____24682 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24682) &&
                        (let uu____24686 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24686) in
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
                      let uu____24702 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24702 = FStar_Syntax_Util.Equal in
                    let uu____24703 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24703
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24704 = equal t1 t2 in
                         (if uu____24704
                          then
                            let uu____24705 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24705
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24708 =
                            let uu____24715 = equal t1 t2 in
                            if uu____24715
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24725 = mk_eq2 wl env orig t1 t2 in
                               match uu____24725 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24708 with
                          | (guard, wl1) ->
                              let uu____24746 = solve_prob orig guard [] wl1 in
                              solve env uu____24746))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____24748,
                 FStar_Syntax_Syntax.Tm_let uu____24749) ->
                  let uu____24774 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____24774
                  then
                    let uu____24775 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____24775
                  else
                    (let uu____24777 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____24777 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____24778, uu____24779) ->
                  let uu____24792 =
                    let uu____24797 =
                      let uu____24798 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24799 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24800 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24801 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24798 uu____24799 uu____24800 uu____24801 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24797) in
                  FStar_Errors.raise_error uu____24792
                    t1.FStar_Syntax_Syntax.pos
              | (uu____24802, FStar_Syntax_Syntax.Tm_let uu____24803) ->
                  let uu____24816 =
                    let uu____24821 =
                      let uu____24822 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24823 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24824 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24825 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24822 uu____24823 uu____24824 uu____24825 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24821) in
                  FStar_Errors.raise_error uu____24816
                    t1.FStar_Syntax_Syntax.pos
              | uu____24826 ->
                  let uu____24831 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____24831 orig))))
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
          (let uu____24893 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____24893
           then
             let uu____24894 =
               let uu____24895 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____24895 in
             let uu____24896 =
               let uu____24897 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____24897 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____24894 uu____24896
           else ());
          (let uu____24899 =
             let uu____24900 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____24900 in
           if uu____24899
           then
             let uu____24901 =
               mklstr
                 (fun uu____24908 ->
                    let uu____24909 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____24910 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____24909 uu____24910) in
             giveup env uu____24901 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____24928 =
                  mklstr
                    (fun uu____24935 ->
                       let uu____24936 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____24937 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____24936 uu____24937) in
                giveup env uu____24928 orig)
             else
               (let uu____24939 =
                  FStar_List.fold_left2
                    (fun uu____24960 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____24960 with
                           | (univ_sub_probs, wl1) ->
                               let uu____24981 =
                                 let uu____24986 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____24987 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____24986
                                   FStar_TypeChecker_Common.EQ uu____24987
                                   "effect universes" in
                               (match uu____24981 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____24939 with
                | (univ_sub_probs, wl1) ->
                    let uu____25006 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____25006 with
                     | (ret_sub_prob, wl2) ->
                         let uu____25013 =
                           FStar_List.fold_right2
                             (fun uu____25050 ->
                                fun uu____25051 ->
                                  fun uu____25052 ->
                                    match (uu____25050, uu____25051,
                                            uu____25052)
                                    with
                                    | ((a1, uu____25096), (a2, uu____25098),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____25131 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____25131 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____25013 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____25157 =
                                  let uu____25160 =
                                    let uu____25163 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____25163 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____25160 in
                                FStar_List.append univ_sub_probs uu____25157 in
                              let guard =
                                let guard =
                                  let uu____25182 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____25182 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3648_25191 = wl3 in
                                {
                                  attempting = (uu___3648_25191.attempting);
                                  wl_deferred = (uu___3648_25191.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3648_25191.wl_deferred_to_tac);
                                  ctr = (uu___3648_25191.ctr);
                                  defer_ok = (uu___3648_25191.defer_ok);
                                  smt_ok = (uu___3648_25191.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3648_25191.umax_heuristic_ok);
                                  tcenv = (uu___3648_25191.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3648_25191.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____25193 = attempt sub_probs wl5 in
                              solve env uu____25193)))) in
        let solve_layered_sub c11 c21 =
          (let uu____25206 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____25206
           then
             let uu____25207 =
               let uu____25208 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25208
                 FStar_Syntax_Print.comp_to_string in
             let uu____25209 =
               let uu____25210 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____25210
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____25207 uu____25209
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____25215 =
                 let uu____25216 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25216 FStar_Ident.string_of_id in
               let uu____25217 =
                 let uu____25218 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____25218 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____25215 uu____25217 in
             let lift_c1 edge =
               let uu____25233 =
                 let uu____25238 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____25238
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____25233
                 (fun uu____25255 ->
                    match uu____25255 with
                    | (c, g) ->
                        let uu____25266 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____25266, g)) in
             let uu____25267 =
               let uu____25278 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____25278 with
               | FStar_Pervasives_Native.None ->
                   let uu____25291 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____25291 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____25307 = lift_c1 edge in
                        (match uu____25307 with
                         | (c12, g_lift) ->
                             let uu____25324 =
                               let uu____25327 =
                                 let uu____25328 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____25328
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____25327
                                 (fun ts ->
                                    let uu____25334 =
                                      let uu____25335 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____25335
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____25334
                                      (fun uu____25346 ->
                                         FStar_Pervasives_Native.Some
                                           uu____25346)) in
                             (c12, g_lift, uu____25324, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____25350 =
                     let uu____25353 =
                       let uu____25354 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____25354
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____25353
                       (fun uu____25365 ->
                          FStar_Pervasives_Native.Some uu____25365) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____25350,
                     true) in
             match uu____25267 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____25376 =
                     mklstr
                       (fun uu____25383 ->
                          let uu____25384 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____25385 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____25384 uu____25385) in
                   giveup env uu____25376 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3683_25391 = wl in
                      {
                        attempting = (uu___3683_25391.attempting);
                        wl_deferred = (uu___3683_25391.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3683_25391.wl_deferred_to_tac);
                        ctr = (uu___3683_25391.ctr);
                        defer_ok = (uu___3683_25391.defer_ok);
                        smt_ok = (uu___3683_25391.smt_ok);
                        umax_heuristic_ok =
                          (uu___3683_25391.umax_heuristic_ok);
                        tcenv = (uu___3683_25391.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3683_25391.repr_subcomp_allowed)
                      } in
                    let uu____25392 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____25414 =
                             let uu____25415 = FStar_Syntax_Subst.compress t in
                             uu____25415.FStar_Syntax_Syntax.n in
                           match uu____25414 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____25418 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____25432)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____25438) ->
                               is_uvar t1
                           | uu____25463 -> false in
                         FStar_List.fold_right2
                           (fun uu____25496 ->
                              fun uu____25497 ->
                                fun uu____25498 ->
                                  match (uu____25496, uu____25497,
                                          uu____25498)
                                  with
                                  | ((a1, uu____25542), (a2, uu____25544),
                                     (is_sub_probs, wl2)) ->
                                      let uu____25577 = is_uvar a1 in
                                      if uu____25577
                                      then
                                        ((let uu____25585 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____25585
                                          then
                                            let uu____25586 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____25587 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____25586 uu____25587
                                          else ());
                                         (let uu____25589 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____25589 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____25392 with
                    | (is_sub_probs, wl2) ->
                        let uu____25615 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____25615 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____25628 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____25629 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____25628 s uu____25629 in
                             let uu____25630 =
                               let uu____25659 =
                                 let uu____25660 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____25660.FStar_Syntax_Syntax.n in
                               match uu____25659 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____25719 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____25719 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____25782 =
                                          let uu____25801 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____25801
                                            (fun uu____25904 ->
                                               match uu____25904 with
                                               | (l1, l2) ->
                                                   let uu____25977 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____25977)) in
                                        (match uu____25782 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____26082 ->
                                   let uu____26083 =
                                     let uu____26088 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____26088) in
                                   FStar_Errors.raise_error uu____26083 r in
                             (match uu____25630 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____26161 =
                                    let uu____26168 =
                                      let uu____26169 =
                                        let uu____26170 =
                                          let uu____26177 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____26177,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____26170 in
                                      [uu____26169] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____26168
                                      (fun b ->
                                         let uu____26193 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____26194 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____26195 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____26193 uu____26194
                                           uu____26195) r in
                                  (match uu____26161 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3748_26203 = wl3 in
                                         {
                                           attempting =
                                             (uu___3748_26203.attempting);
                                           wl_deferred =
                                             (uu___3748_26203.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3748_26203.wl_deferred_to_tac);
                                           ctr = (uu___3748_26203.ctr);
                                           defer_ok =
                                             (uu___3748_26203.defer_ok);
                                           smt_ok = (uu___3748_26203.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3748_26203.umax_heuristic_ok);
                                           tcenv = (uu___3748_26203.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3748_26203.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____26228 =
                                                  let uu____26235 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____26235, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____26228) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____26252 =
                                         let f_sort_is =
                                           let uu____26262 =
                                             let uu____26265 =
                                               let uu____26266 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____26266.FStar_Syntax_Syntax.sort in
                                             let uu____26275 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____26276 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____26265 uu____26275 r
                                               uu____26276 in
                                           FStar_All.pipe_right uu____26262
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____26281 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____26317 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____26317 with
                                                  | (ps, wl5) ->
                                                      ((let uu____26339 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____26339
                                                        then
                                                          let uu____26340 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____26341 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____26340
                                                            uu____26341
                                                        else ());
                                                       (let uu____26343 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____26343
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____26281 in
                                       (match uu____26252 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____26367 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____26367
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____26368 =
                                              let g_sort_is =
                                                let uu____26378 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____26379 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____26378 r uu____26379 in
                                              let uu____26380 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____26416 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____26416 with
                                                       | (ps, wl6) ->
                                                           ((let uu____26438
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____26438
                                                             then
                                                               let uu____26439
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____26440
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____26439
                                                                 uu____26440
                                                             else ());
                                                            (let uu____26442
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____26442
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____26380 in
                                            (match uu____26368 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____26468 =
                                                     let uu____26473 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____26474 =
                                                       let uu____26475 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____26475 in
                                                     (uu____26473,
                                                       uu____26474) in
                                                   match uu____26468 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____26503 =
                                                     let uu____26506 =
                                                       let uu____26509 =
                                                         let uu____26512 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____26512 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____26509 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____26506 in
                                                   ret_sub_prob ::
                                                     uu____26503 in
                                                 let guard =
                                                   let guard =
                                                     let uu____26533 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____26533 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____26544 =
                                                     let uu____26547 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____26550 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____26550)
                                                       uu____26547 in
                                                   solve_prob orig
                                                     uu____26544 [] wl6 in
                                                 let uu____26551 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____26551))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____26576 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____26578 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____26578]
               | x -> x in
             let c12 =
               let uu___3806_26581 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3806_26581.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3806_26581.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3806_26581.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3806_26581.FStar_Syntax_Syntax.flags)
               } in
             let uu____26582 =
               let uu____26587 =
                 FStar_All.pipe_right
                   (let uu___3809_26589 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3809_26589.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3809_26589.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3809_26589.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3809_26589.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____26587
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____26582
               (fun uu____26603 ->
                  match uu____26603 with
                  | (c, g) ->
                      let uu____26610 =
                        let uu____26611 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____26611 in
                      if uu____26610
                      then
                        let uu____26612 =
                          let uu____26617 =
                            let uu____26618 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____26619 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____26618 uu____26619 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____26617) in
                        FStar_Errors.raise_error uu____26612 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____26621 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____26623 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____26623))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____26621
           then
             let uu____26624 =
               mklstr
                 (fun uu____26631 ->
                    let uu____26632 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____26633 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____26632 uu____26633) in
             giveup env uu____26624 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_26639 ->
                        match uu___29_26639 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____26640 -> false)) in
              let uu____26641 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____26675)::uu____26676,
                   (wp2, uu____26678)::uu____26679) -> (wp1, wp2)
                | uu____26754 ->
                    let uu____26779 =
                      let uu____26784 =
                        let uu____26785 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____26786 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____26785 uu____26786 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____26784) in
                    FStar_Errors.raise_error uu____26779
                      env.FStar_TypeChecker_Env.range in
              match uu____26641 with
              | (wpc1, wpc2) ->
                  let uu____26799 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____26799
                  then
                    let uu____26802 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____26802 wl
                  else
                    (let uu____26804 =
                       let uu____26811 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____26811 in
                     match uu____26804 with
                     | (c2_decl, qualifiers) ->
                         let uu____26832 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____26832
                         then
                           let c1_repr =
                             let uu____26836 =
                               let uu____26837 =
                                 let uu____26838 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____26838 in
                               let uu____26839 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26837 uu____26839 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26836 in
                           let c2_repr =
                             let uu____26841 =
                               let uu____26842 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____26843 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26842 uu____26843 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26841 in
                           let uu____26844 =
                             let uu____26849 =
                               let uu____26850 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____26851 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____26850 uu____26851 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____26849 in
                           (match uu____26844 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____26855 = attempt [prob] wl2 in
                                solve env uu____26855)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____26872 = lift_c1 () in
                                   FStar_All.pipe_right uu____26872
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____26894 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____26894
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____26898 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____26898 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____26904 =
                                       let uu____26905 =
                                         let uu____26922 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____26925 =
                                           let uu____26936 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____26936; wpc1_2] in
                                         (uu____26922, uu____26925) in
                                       FStar_Syntax_Syntax.Tm_app uu____26905 in
                                     FStar_Syntax_Syntax.mk uu____26904 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____26984 =
                                      let uu____26985 =
                                        let uu____27002 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____27005 =
                                          let uu____27016 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____27025 =
                                            let uu____27036 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____27036; wpc1_2] in
                                          uu____27016 :: uu____27025 in
                                        (uu____27002, uu____27005) in
                                      FStar_Syntax_Syntax.Tm_app uu____26985 in
                                    FStar_Syntax_Syntax.mk uu____26984 r)) in
                            (let uu____27090 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____27090
                             then
                               let uu____27091 =
                                 let uu____27092 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____27092 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____27091
                             else ());
                            (let uu____27094 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____27094 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____27102 =
                                     let uu____27105 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____27108 ->
                                          FStar_Pervasives_Native.Some
                                            uu____27108) uu____27105 in
                                   solve_prob orig uu____27102 [] wl1 in
                                 let uu____27109 = attempt [base_prob] wl2 in
                                 solve env uu____27109))))) in
        let uu____27110 = FStar_Util.physical_equality c1 c2 in
        if uu____27110
        then
          let uu____27111 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____27111
        else
          ((let uu____27114 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____27114
            then
              let uu____27115 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____27116 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____27115
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____27116
            else ());
           (let uu____27118 =
              let uu____27127 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____27130 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____27127, uu____27130) in
            match uu____27118 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____27148),
                    FStar_Syntax_Syntax.Total (t2, uu____27150)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____27167 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27167 wl
                 | (FStar_Syntax_Syntax.GTotal uu____27168,
                    FStar_Syntax_Syntax.Total uu____27169) ->
                     let uu____27186 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____27186 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____27188),
                    FStar_Syntax_Syntax.Total (t2, uu____27190)) ->
                     let uu____27207 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27207 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____27209),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27211)) ->
                     let uu____27228 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27228 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27230),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27232)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____27249 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27249 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27251),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27253)) ->
                     let uu____27270 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____27270 orig
                 | (FStar_Syntax_Syntax.GTotal uu____27271,
                    FStar_Syntax_Syntax.Comp uu____27272) ->
                     let uu____27281 =
                       let uu___3933_27284 = problem in
                       let uu____27287 =
                         let uu____27288 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27288 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3933_27284.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27287;
                         FStar_TypeChecker_Common.relation =
                           (uu___3933_27284.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3933_27284.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3933_27284.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3933_27284.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3933_27284.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3933_27284.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3933_27284.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3933_27284.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27281 wl
                 | (FStar_Syntax_Syntax.Total uu____27289,
                    FStar_Syntax_Syntax.Comp uu____27290) ->
                     let uu____27299 =
                       let uu___3933_27302 = problem in
                       let uu____27305 =
                         let uu____27306 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27306 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3933_27302.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27305;
                         FStar_TypeChecker_Common.relation =
                           (uu___3933_27302.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3933_27302.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3933_27302.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3933_27302.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3933_27302.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3933_27302.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3933_27302.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3933_27302.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27299 wl
                 | (FStar_Syntax_Syntax.Comp uu____27307,
                    FStar_Syntax_Syntax.GTotal uu____27308) ->
                     let uu____27317 =
                       let uu___3945_27320 = problem in
                       let uu____27323 =
                         let uu____27324 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27324 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3945_27320.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3945_27320.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3945_27320.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27323;
                         FStar_TypeChecker_Common.element =
                           (uu___3945_27320.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3945_27320.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3945_27320.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3945_27320.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3945_27320.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3945_27320.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27317 wl
                 | (FStar_Syntax_Syntax.Comp uu____27325,
                    FStar_Syntax_Syntax.Total uu____27326) ->
                     let uu____27335 =
                       let uu___3945_27338 = problem in
                       let uu____27341 =
                         let uu____27342 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27342 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3945_27338.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3945_27338.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3945_27338.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27341;
                         FStar_TypeChecker_Common.element =
                           (uu___3945_27338.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3945_27338.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3945_27338.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3945_27338.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3945_27338.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3945_27338.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27335 wl
                 | (FStar_Syntax_Syntax.Comp uu____27343,
                    FStar_Syntax_Syntax.Comp uu____27344) ->
                     let uu____27345 =
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
                     if uu____27345
                     then
                       let uu____27346 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____27346 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27350 =
                            let uu____27355 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____27355
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27361 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____27362 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____27361, uu____27362)) in
                          match uu____27350 with
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
                           (let uu____27369 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____27369
                            then
                              let uu____27370 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____27371 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____27370 uu____27371
                            else ());
                           (let uu____27373 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____27373
                            then solve_layered_sub c12 c22
                            else
                              (let uu____27375 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____27375 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____27378 =
                                     mklstr
                                       (fun uu____27385 ->
                                          let uu____27386 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____27387 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____27386 uu____27387) in
                                   giveup env uu____27378 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____27394 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____27394 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____27435 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____27435 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____27453 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27481 ->
                match uu____27481 with
                | (u1, u2) ->
                    let uu____27488 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____27489 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____27488 uu____27489)) in
      FStar_All.pipe_right uu____27453 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial, [], (uu____27516, [])) when
          let uu____27541 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____27541 -> "{}"
      | uu____27542 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27565 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____27565
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____27585 =
              FStar_List.map
                (fun uu____27596 ->
                   match uu____27596 with
                   | (msg, x) ->
                       let uu____27603 =
                         let uu____27604 = prob_to_string env x in
                         Prims.op_Hat ": " uu____27604 in
                       Prims.op_Hat msg uu____27603) defs in
            FStar_All.pipe_right uu____27585 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____27608 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____27609 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____27610 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____27608 uu____27609 uu____27610 imps
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
                  let uu____27663 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____27663
                  then
                    let uu____27664 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____27665 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27664
                      (rel_to_string rel) uu____27665
                  else "TOP" in
                let uu____27667 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____27667 with
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
              let uu____27725 =
                let uu____27728 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____27731 ->
                     FStar_Pervasives_Native.Some uu____27731) uu____27728 in
              FStar_Syntax_Syntax.new_bv uu____27725 t1 in
            let uu____27732 =
              let uu____27737 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27737 in
            match uu____27732 with | (p, wl1) -> (p, x, wl1)
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
        (let uu____27808 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____27808
         then
           let uu____27809 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____27809
         else ());
        (let uu____27813 =
           FStar_Util.record_time (fun uu____27819 -> solve env probs) in
         match uu____27813 with
         | (sol, ms) ->
             ((let uu____27831 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____27831
               then
                 let uu____27832 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____27832
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____27845 =
                     FStar_Util.record_time
                       (fun uu____27851 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____27845 with
                    | ((), ms1) ->
                        ((let uu____27862 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____27862
                          then
                            let uu____27863 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____27863
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____27874 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____27874
                     then
                       let uu____27875 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____27875
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
          ((let uu____27899 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____27899
            then
              let uu____27900 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27900
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____27904 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____27904
             then
               let uu____27905 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27905
             else ());
            (let f2 =
               let uu____27908 =
                 let uu____27909 = FStar_Syntax_Util.unmeta f1 in
                 uu____27909.FStar_Syntax_Syntax.n in
               match uu____27908 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27913 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4065_27914 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4065_27914.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4065_27914.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4065_27914.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4065_27914.FStar_TypeChecker_Common.implicits)
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
            let uu____27965 =
              let uu____27966 =
                let uu____27967 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____27968 ->
                       FStar_TypeChecker_Common.NonTrivial uu____27968) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____27967;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____27966 in
            FStar_All.pipe_left
              (fun uu____27975 -> FStar_Pervasives_Native.Some uu____27975)
              uu____27965
let with_guard_no_simp :
  'uuuuuu27984 .
    'uuuuuu27984 ->
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
            let uu____28033 =
              let uu____28034 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____28035 ->
                     FStar_TypeChecker_Common.NonTrivial uu____28035) in
              {
                FStar_TypeChecker_Common.guard_f = uu____28034;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____28033
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
          (let uu____28065 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____28065
           then
             let uu____28066 = FStar_Syntax_Print.term_to_string t1 in
             let uu____28067 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____28066
               uu____28067
           else ());
          (let uu____28069 =
             let uu____28074 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____28074 in
           match uu____28069 with
           | (prob, wl) ->
               let g =
                 let uu____28082 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____28092 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____28082 in
               ((let uu____28114 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____28114
                 then
                   let uu____28115 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____28115
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
        let uu____28132 = try_teq true env t1 t2 in
        match uu____28132 with
        | FStar_Pervasives_Native.None ->
            ((let uu____28136 = FStar_TypeChecker_Env.get_range env in
              let uu____28137 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____28136 uu____28137);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____28144 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____28144
              then
                let uu____28145 = FStar_Syntax_Print.term_to_string t1 in
                let uu____28146 = FStar_Syntax_Print.term_to_string t2 in
                let uu____28147 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____28145
                  uu____28146 uu____28147
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
        (let uu____28167 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____28167
         then
           let uu____28168 = FStar_Syntax_Print.term_to_string t1 in
           let uu____28169 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____28168
             uu____28169
         else ());
        (let uu____28171 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____28171 with
         | (prob, x, wl) ->
             let g =
               let uu____28186 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____28196 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____28186 in
             ((let uu____28218 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____28218
               then
                 let uu____28219 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____28219
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____28224 =
                     let uu____28225 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____28225 g1 in
                   FStar_Pervasives_Native.Some uu____28224)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____28246 = FStar_TypeChecker_Env.get_range env in
          let uu____28247 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____28246 uu____28247
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
        (let uu____28272 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____28272
         then
           let uu____28273 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____28274 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28273 uu____28274
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28277 =
           let uu____28284 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28284 "sub_comp" in
         match uu____28277 with
         | (prob, wl) ->
             let wl1 =
               let uu___4138_28294 = wl in
               {
                 attempting = (uu___4138_28294.attempting);
                 wl_deferred = (uu___4138_28294.wl_deferred);
                 wl_deferred_to_tac = (uu___4138_28294.wl_deferred_to_tac);
                 ctr = (uu___4138_28294.ctr);
                 defer_ok = (uu___4138_28294.defer_ok);
                 smt_ok = (uu___4138_28294.smt_ok);
                 umax_heuristic_ok = (uu___4138_28294.umax_heuristic_ok);
                 tcenv = (uu___4138_28294.tcenv);
                 wl_implicits = (uu___4138_28294.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____28297 =
                 FStar_Util.record_time
                   (fun uu____28308 ->
                      let uu____28309 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____28319 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____28309) in
               match uu____28297 with
               | (r, ms) ->
                   ((let uu____28349 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____28349
                     then
                       let uu____28350 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____28351 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____28352 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28350 uu____28351
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28352
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
      fun uu____28381 ->
        match uu____28381 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28424 =
                 let uu____28429 =
                   let uu____28430 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____28431 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28430 uu____28431 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28429) in
               let uu____28432 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____28424 uu____28432) in
            let equiv v v' =
              let uu____28444 =
                let uu____28449 = FStar_Syntax_Subst.compress_univ v in
                let uu____28450 = FStar_Syntax_Subst.compress_univ v' in
                (uu____28449, uu____28450) in
              match uu____28444 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28473 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____28503 = FStar_Syntax_Subst.compress_univ v in
                      match uu____28503 with
                      | FStar_Syntax_Syntax.U_unif uu____28510 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28541 ->
                                    match uu____28541 with
                                    | (u, v') ->
                                        let uu____28550 = equiv v v' in
                                        if uu____28550
                                        then
                                          let uu____28553 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____28553 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____28569 -> [])) in
            let uu____28574 =
              let wl =
                let uu___4181_28578 = empty_worklist env in
                {
                  attempting = (uu___4181_28578.attempting);
                  wl_deferred = (uu___4181_28578.wl_deferred);
                  wl_deferred_to_tac = (uu___4181_28578.wl_deferred_to_tac);
                  ctr = (uu___4181_28578.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4181_28578.smt_ok);
                  umax_heuristic_ok = (uu___4181_28578.umax_heuristic_ok);
                  tcenv = (uu___4181_28578.tcenv);
                  wl_implicits = (uu___4181_28578.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4181_28578.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28596 ->
                      match uu____28596 with
                      | (lb, v) ->
                          let uu____28603 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____28603 with
                           | USolved wl1 -> ()
                           | uu____28605 -> fail lb v))) in
            let rec check_ineq uu____28615 =
              match uu____28615 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____28624) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____28651,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____28653,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____28666) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____28673, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____28681 -> false) in
            let uu____28686 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28701 ->
                      match uu____28701 with
                      | (u, v) ->
                          let uu____28708 = check_ineq (u, v) in
                          if uu____28708
                          then true
                          else
                            ((let uu____28711 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____28711
                              then
                                let uu____28712 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____28713 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____28712
                                  uu____28713
                              else ());
                             false))) in
            if uu____28686
            then ()
            else
              ((let uu____28717 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____28717
                then
                  ((let uu____28719 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28719);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28729 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28729))
                else ());
               (let uu____28739 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28739))
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
          let fail uu____28813 =
            match uu____28813 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4259_28838 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4259_28838.attempting);
              wl_deferred = (uu___4259_28838.wl_deferred);
              wl_deferred_to_tac = (uu___4259_28838.wl_deferred_to_tac);
              ctr = (uu___4259_28838.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4259_28838.umax_heuristic_ok);
              tcenv = (uu___4259_28838.tcenv);
              wl_implicits = (uu___4259_28838.wl_implicits);
              repr_subcomp_allowed = (uu___4259_28838.repr_subcomp_allowed)
            } in
          (let uu____28840 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____28840
           then
             let uu____28841 = FStar_Util.string_of_bool defer_ok in
             let uu____28842 = wl_to_string wl in
             let uu____28843 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____28841 uu____28842 uu____28843
           else ());
          (let g1 =
             let uu____28846 = solve_and_commit env wl fail in
             match uu____28846 with
             | FStar_Pervasives_Native.Some
                 (uu____28855::uu____28856, uu____28857, uu____28858) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4276_28888 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4276_28888.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4276_28888.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____28893 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____28905 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____28905
             then
               let uu____28906 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____28906
             else ());
            (let uu___4284_28908 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4284_28908.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4284_28908.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4284_28908.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4284_28908.FStar_TypeChecker_Common.implicits)
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
          (let uu____28983 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____28983
           then
             let uu____28984 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____28984
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4301_28988 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4301_28988.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4301_28988.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4301_28988.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4301_28988.FStar_TypeChecker_Common.implicits)
             } in
           let uu____28989 =
             let uu____28990 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____28990 in
           if uu____28989
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____28998 = FStar_TypeChecker_Env.get_range env in
                      let uu____28999 =
                        let uu____29000 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____29000 in
                      FStar_Errors.diag uu____28998 uu____28999)
                   else ();
                   (let vc1 =
                      let uu____29003 =
                        let uu____29006 =
                          let uu____29007 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____29007 in
                        FStar_Pervasives_Native.Some uu____29006 in
                      FStar_Profiling.profile
                        (fun uu____29009 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____29003 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____29011 = FStar_TypeChecker_Env.get_range env in
                       let uu____29012 =
                         let uu____29013 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____29013 in
                       FStar_Errors.diag uu____29011 uu____29012)
                    else ();
                    (let uu____29016 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____29016 "discharge_guard'" env vc1);
                    (let uu____29017 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____29017 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____29024 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____29025 =
                                 let uu____29026 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____29026 in
                               FStar_Errors.diag uu____29024 uu____29025)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____29031 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____29032 =
                                 let uu____29033 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____29033 in
                               FStar_Errors.diag uu____29031 uu____29032)
                            else ();
                            (let vcs =
                               let uu____29044 = FStar_Options.use_tactics () in
                               if uu____29044
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____29064 ->
                                      (let uu____29066 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____29067 -> ()) uu____29066);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____29110 ->
                                               match uu____29110 with
                                               | (env1, goal, opts) ->
                                                   let uu____29126 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____29126, opts)))))
                               else
                                 (let uu____29128 =
                                    let uu____29135 = FStar_Options.peek () in
                                    (env, vc2, uu____29135) in
                                  [uu____29128]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____29168 ->
                                     match uu____29168 with
                                     | (env1, goal, opts) ->
                                         let uu____29178 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____29178 with
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
                                                 (let uu____29185 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____29186 =
                                                    let uu____29187 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____29188 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____29187 uu____29188 in
                                                  FStar_Errors.diag
                                                    uu____29185 uu____29186)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____29191 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____29192 =
                                                    let uu____29193 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____29193 in
                                                  FStar_Errors.diag
                                                    uu____29191 uu____29192)
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
      let uu____29207 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____29207 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____29214 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____29214
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____29225 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____29225 with
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
        let uu____29251 = try_teq false env t1 t2 in
        match uu____29251 with
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
             let uu____29294 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____29294 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____29304 =
                   let uu____29305 = FStar_Syntax_Subst.compress t_norm in
                   uu____29305.FStar_Syntax_Syntax.n in
                 (match uu____29304 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____29311 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29311
                        (fun uu____29314 ->
                           FStar_Pervasives_Native.Some uu____29314)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____29316) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____29321 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29321
                        (fun uu____29324 ->
                           FStar_Pervasives_Native.Some uu____29324)
                  | uu____29325 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____29335 =
                      let uu____29336 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____29336 FStar_Util.is_none in
                    if uu____29335
                    then
                      let uu____29341 = imp_value imp in
                      match uu____29341 with
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
        let uu____29362 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____29362 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____29380 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____29380 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____29384 ->
                       let uu____29385 =
                         let uu____29386 = FStar_Syntax_Subst.compress r in
                         uu____29386.FStar_Syntax_Syntax.n in
                       (match uu____29385 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____29390)
                            -> unresolved ctx_u'
                        | uu____29407 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____29427 = acc in
              match uu____29427 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____29434 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____29434 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____29447 = hd in
                       (match uu____29447 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____29453 = unresolved ctx_u in
                               if uu____29453
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____29462 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____29462
                                       then
                                         let uu____29463 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____29463
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____29469 =
                                           teq_nosmt env1 t tm in
                                         match uu____29469 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4446_29478 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4446_29478.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4446_29478.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4446_29478.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4446_29478.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4446_29478.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4446_29478.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4446_29478.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4449_29480 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4449_29480.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4449_29480.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4449_29480.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____29481 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4454_29487 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4454_29487.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4454_29487.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4454_29487.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4454_29487.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4454_29487.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4454_29487.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4454_29487.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4454_29487.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4454_29487.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4454_29487.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4454_29487.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4454_29487.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4454_29487.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4454_29487.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4454_29487.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4454_29487.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4454_29487.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4454_29487.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4454_29487.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4454_29487.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4454_29487.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4454_29487.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4454_29487.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4454_29487.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4454_29487.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4454_29487.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4454_29487.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4454_29487.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4454_29487.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4454_29487.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4454_29487.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4454_29487.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4454_29487.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4454_29487.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4454_29487.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4454_29487.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4454_29487.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4459_29490 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4459_29490.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4459_29490.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4459_29490.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4459_29490.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4459_29490.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4459_29490.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4459_29490.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4459_29490.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4459_29490.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4459_29490.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4459_29490.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4459_29490.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4459_29490.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4459_29490.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4459_29490.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4459_29490.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4459_29490.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4459_29490.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4459_29490.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4459_29490.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4459_29490.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4459_29490.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4459_29490.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4459_29490.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4459_29490.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4459_29490.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4459_29490.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4459_29490.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4459_29490.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4459_29490.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4459_29490.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4459_29490.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____29493 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29493
                                     then
                                       let uu____29494 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____29495 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____29496 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____29497 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____29494 uu____29495 uu____29496
                                         reason uu____29497
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4465_29501 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____29508 =
                                               let uu____29517 =
                                                 let uu____29524 =
                                                   let uu____29525 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____29526 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____29527 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____29525 uu____29526
                                                     uu____29527 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____29524, r) in
                                               [uu____29517] in
                                             FStar_Errors.add_errors
                                               uu____29508);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____29541 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____29551 ->
                                                 let uu____29552 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____29553 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____29554 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____29552 uu____29553
                                                   reason uu____29554)) env2
                                           g1 true in
                                       match uu____29541 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4477_29556 = g in
            let uu____29557 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4477_29556.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4477_29556.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4477_29556.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4477_29556.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____29557
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____29569 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29569
       then
         let uu____29570 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____29570
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
      (let uu____29593 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29593
       then
         let uu____29594 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____29594
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____29598 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____29599 -> ()) uu____29598
       | imp::uu____29601 ->
           let uu____29604 =
             let uu____29609 =
               let uu____29610 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____29611 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____29610 uu____29611
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29609) in
           FStar_Errors.raise_error uu____29604
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29627 = teq env t1 t2 in
        force_trivial_guard env uu____29627
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29643 = teq_nosmt env t1 t2 in
        match uu____29643 with
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
          (let uu____29673 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____29673
           then
             let uu____29674 =
               let uu____29675 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____29675
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____29681 = FStar_Syntax_Print.term_to_string t1 in
             let uu____29682 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____29674
               uu____29681 uu____29682
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4515_29694 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4515_29694.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4515_29694.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4515_29694.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4515_29694.FStar_TypeChecker_Common.implicits)
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
        (let uu____29729 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29729
         then
           let uu____29730 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29731 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29730
             uu____29731
         else ());
        (let uu____29733 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29733 with
         | (prob, x, wl) ->
             let g =
               let uu____29752 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29762 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29752 in
             ((let uu____29784 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____29784
               then
                 let uu____29785 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____29786 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____29787 =
                   let uu____29788 = FStar_Util.must g in
                   guard_to_string env uu____29788 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29785 uu____29786 uu____29787
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
        let uu____29822 = check_subtyping env t1 t2 in
        match uu____29822 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29841 =
              let uu____29842 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____29842 g in
            FStar_Pervasives_Native.Some uu____29841
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29860 = check_subtyping env t1 t2 in
        match uu____29860 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29879 =
              let uu____29880 =
                let uu____29881 = FStar_Syntax_Syntax.mk_binder x in
                [uu____29881] in
              FStar_TypeChecker_Env.close_guard env uu____29880 g in
            FStar_Pervasives_Native.Some uu____29879
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____29918 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29918
         then
           let uu____29919 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29920 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____29919
             uu____29920
         else ());
        (let uu____29922 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29922 with
         | (prob, x, wl) ->
             let g =
               let uu____29937 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____29947 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29937 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____29972 =
                      let uu____29973 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____29973] in
                    FStar_TypeChecker_Env.close_guard env uu____29972 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____30010 = subtype_nosmt env t1 t2 in
        match uu____30010 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)