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
          let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl in
          let wl2 =
            let uu___1816_11344 = wl1 in
            let uu____11345 =
              let uu____11354 =
                let uu____11361 = FStar_Thunk.mkv reason in
                ((wl1.ctr), uu____11361, orig) in
              uu____11354 :: (wl1.wl_deferred_to_tac) in
            {
              attempting = (uu___1816_11344.attempting);
              wl_deferred = (uu___1816_11344.wl_deferred);
              wl_deferred_to_tac = uu____11345;
              ctr = (uu___1816_11344.ctr);
              defer_ok = (uu___1816_11344.defer_ok);
              smt_ok = (uu___1816_11344.smt_ok);
              umax_heuristic_ok = (uu___1816_11344.umax_heuristic_ok);
              tcenv = (uu___1816_11344.tcenv);
              wl_implicits = (uu___1816_11344.wl_implicits);
              repr_subcomp_allowed = (uu___1816_11344.repr_subcomp_allowed)
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
                let uu____11384 = FStar_Syntax_Util.head_and_args t in
                match uu____11384 with
                | (head, uu____11406) ->
                    let uu____11431 =
                      let uu____11432 = FStar_Syntax_Subst.compress head in
                      uu____11432.FStar_Syntax_Syntax.n in
                    (match uu____11431 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu____11440) ->
                         let uu____11457 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu____11457,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____11458 -> (false, "")) in
              let uu____11459 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu____11459 with
               | (l1, r1) ->
                   let uu____11466 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu____11466 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____11474 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl in
                           solve env uu____11474)))
          | uu____11475 ->
              let uu____11476 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu____11476
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
               let uu____11560 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu____11560 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu____11613 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu____11613
                then
                  let uu____11614 = FStar_Syntax_Print.term_to_string t1 in
                  let uu____11615 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____11614 uu____11615
                else ());
               (let uu____11617 = head_matches_delta env1 wl2 t1 t2 in
                match uu____11617 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu____11662 = eq_prob t1 t2 wl2 in
                         (match uu____11662 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu____11683 ->
                         let uu____11692 = eq_prob t1 t2 wl2 in
                         (match uu____11692 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu____11741 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu____11756 =
                                 FStar_Syntax_Subst.compress t11 in
                               let uu____11757 =
                                 FStar_Syntax_Subst.compress t21 in
                               (uu____11756, uu____11757)
                           | FStar_Pervasives_Native.None ->
                               let uu____11762 =
                                 FStar_Syntax_Subst.compress t1 in
                               let uu____11763 =
                                 FStar_Syntax_Subst.compress t2 in
                               (uu____11762, uu____11763) in
                         (match uu____11741 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____11794 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu____11794 with
                                | (t1_hd, t1_args) ->
                                    let uu____11839 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu____11839 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____11903 =
                                              let uu____11910 =
                                                let uu____11921 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu____11921 :: t1_args in
                                              let uu____11938 =
                                                let uu____11947 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu____11947 :: t2_args in
                                              FStar_List.fold_left2
                                                (fun uu____11996 ->
                                                   fun uu____11997 ->
                                                     fun uu____11998 ->
                                                       match (uu____11996,
                                                               uu____11997,
                                                               uu____11998)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu____12048),
                                                          (a2, uu____12050))
                                                           ->
                                                           let uu____12087 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu____12087
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____11910
                                                uu____11938 in
                                            match uu____11903 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  let uu___1919_12113 = wl4 in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1919_12113.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1919_12113.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1919_12113.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1919_12113.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1919_12113.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____12121 =
                                                  solve env1 wl' in
                                                (match uu____12121 with
                                                 | Success
                                                     (uu____12124,
                                                      defer_to_tac, imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____12128 =
                                                         extend_wl wl4
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu____12128))
                                                 | Failed uu____12129 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu____12161 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu____12161 with
                                | (t1_base, p1_opt) ->
                                    let uu____12196 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu____12196 with
                                     | (t2_base, p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____12294 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu____12294
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
                                               let uu____12342 =
                                                 op phi11 phi21 in
                                               refine x1 uu____12342
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
                                               let uu____12372 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12372
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
                                               let uu____12402 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____12402
                                           | uu____12405 -> t_base in
                                         let uu____12422 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu____12422 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____12436 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu____12436, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu____12443 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu____12443 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu____12478 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu____12478 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu____12513 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu____12513
                                                         with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu____12537 = combine t11 t21 wl2 in
                              (match uu____12537 with
                               | (t12, ps, wl3) ->
                                   ((let uu____12570 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu____12570
                                     then
                                       let uu____12571 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____12571
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu____12610 ts1 =
               match uu____12610 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____12673 = pairwise out t wl2 in
                        (match uu____12673 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2)) in
             let uu____12709 =
               let uu____12720 = FStar_List.hd ts in (uu____12720, [], wl1) in
             let uu____12729 = FStar_List.tl ts in
             aux uu____12709 uu____12729 in
           let uu____12736 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu____12736 with
           | (this_flex, this_rigid) ->
               let uu____12760 =
                 let uu____12761 = FStar_Syntax_Subst.compress this_rigid in
                 uu____12761.FStar_Syntax_Syntax.n in
               (match uu____12760 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu____12786 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu____12786
                    then
                      let uu____12787 = destruct_flex_t this_flex wl in
                      (match uu____12787 with
                       | (flex, wl1) ->
                           let uu____12794 = quasi_pattern env flex in
                           (match uu____12794 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu____12812 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____12812
                                  then
                                    let uu____12813 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____12813
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____12816 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2029_12819 = tp in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2029_12819.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2029_12819.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2029_12819.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2029_12819.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2029_12819.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2029_12819.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2029_12819.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2029_12819.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2029_12819.FStar_TypeChecker_Common.rank)
                                }))] wl in
                       solve env uu____12816)
                | uu____12820 ->
                    ((let uu____12822 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____12822
                      then
                        let uu____12823 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____12823
                      else ());
                     (let uu____12825 =
                        FStar_Syntax_Util.head_and_args this_flex in
                      match uu____12825 with
                      | (u, _args) ->
                          let uu____12868 =
                            let uu____12869 = FStar_Syntax_Subst.compress u in
                            uu____12869.FStar_Syntax_Syntax.n in
                          (match uu____12868 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu____12896 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu____12896 with
                                 | (u', uu____12914) ->
                                     let uu____12939 =
                                       let uu____12940 = whnf env u' in
                                       uu____12940.FStar_Syntax_Syntax.n in
                                     (match uu____12939 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____12961 -> false) in
                               let uu____12962 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_12985 ->
                                         match uu___23_12985 with
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
                                              | uu____12994 -> false)
                                         | uu____12997 -> false)) in
                               (match uu____12962 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu____13011 = whnf env this_rigid in
                                      let uu____13012 =
                                        FStar_List.collect
                                          (fun uu___24_13018 ->
                                             match uu___24_13018 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13024 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu____13024]
                                             | uu____13026 -> [])
                                          bounds_probs in
                                      uu____13011 :: uu____13012 in
                                    let uu____13027 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu____13027 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu____13058 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu____13073 =
                                               let uu____13074 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu____13074.FStar_Syntax_Syntax.n in
                                             match uu____13073 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13086 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13086)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13095 -> bound in
                                           let uu____13096 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu____13096) in
                                         (match uu____13058 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13125 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu____13125
                                                then
                                                  let wl'1 =
                                                    let uu___2089_13127 = wl1 in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2089_13127.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2089_13127.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2089_13127.ctr);
                                                      defer_ok =
                                                        (uu___2089_13127.defer_ok);
                                                      smt_ok =
                                                        (uu___2089_13127.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2089_13127.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2089_13127.tcenv);
                                                      wl_implicits =
                                                        (uu___2089_13127.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2089_13127.repr_subcomp_allowed)
                                                    } in
                                                  let uu____13128 =
                                                    wl_to_string wl'1 in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13128
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____13131 =
                                                  solve_t env eq_prob
                                                    (let uu___2094_13133 =
                                                       wl' in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2094_13133.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2094_13133.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2094_13133.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2094_13133.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2094_13133.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2094_13133.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2094_13133.repr_subcomp_allowed)
                                                     }) in
                                                match uu____13131 with
                                                | Success
                                                    (uu____13134,
                                                     defer_to_tac, imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2101_13138 =
                                                        wl' in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2101_13138.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2101_13138.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2101_13138.ctr);
                                                        defer_ok =
                                                          (uu___2101_13138.defer_ok);
                                                        smt_ok =
                                                          (uu___2101_13138.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2101_13138.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2101_13138.tcenv);
                                                        wl_implicits =
                                                          (uu___2101_13138.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2101_13138.repr_subcomp_allowed)
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
                                                    let uu____13154 =
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
                                                    ((let uu____13165 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu____13165
                                                      then
                                                        let uu____13166 =
                                                          let uu____13167 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_All.pipe_right
                                                            uu____13167
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13166
                                                      else ());
                                                     (let uu____13173 =
                                                        let uu____13188 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu____13188) in
                                                      match uu____13173 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu____13210)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13236 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13236
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
                                                                  let uu____13253
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13253))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____13278 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____13278
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
                                                                    let uu____13296
                                                                    =
                                                                    let uu____13301
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____13301 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____13296
                                                                    [] wl2 in
                                                                  let uu____13306
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____13306))))
                                                      | uu____13307 ->
                                                          let uu____13322 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env
                                                            uu____13322 p)))))))
                           | uu____13325 when flip ->
                               let uu____13326 =
                                 let uu____13327 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13328 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____13327 uu____13328 in
                               failwith uu____13326
                           | uu____13329 ->
                               let uu____13330 =
                                 let uu____13331 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____13332 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____13331 uu____13332 in
                               failwith uu____13330)))))
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
                      (fun uu____13366 ->
                         match uu____13366 with
                         | (x, i) ->
                             let uu____13385 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             (uu____13385, i)) bs_lhs in
                  let uu____13388 = lhs in
                  match uu____13388 with
                  | Flex (uu____13389, u_lhs, uu____13391) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____13488 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____13498 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu____13498, univ) in
                          match uu____13488 with
                          | (k, univ) ->
                              let uu____13505 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2 in
                              (match uu____13505 with
                               | (uu____13522, u, wl3) ->
                                   let uu____13525 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu____13525, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____13551 =
                              let uu____13564 =
                                let uu____13575 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu____13575 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_List.fold_right
                                (fun uu____13626 ->
                                   fun uu____13627 ->
                                     match (uu____13626, uu____13627) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu____13728 =
                                           let uu____13735 =
                                             let uu____13738 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____13738 in
                                           copy_uvar u_lhs [] uu____13735 wl2 in
                                         (match uu____13728 with
                                          | (uu____13767, t_a, wl3) ->
                                              let uu____13770 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu____13770 with
                                               | (uu____13789, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____13564
                                ([], wl1) in
                            (match uu____13551 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_13858 ->
                                        match uu___25_13858 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____13859 -> false
                                        | uu____13862 -> true) flags in
                                 let ct' =
                                   let uu___2220_13864 = ct in
                                   let uu____13865 =
                                     let uu____13868 = FStar_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu____13868 in
                                   let uu____13883 = FStar_List.tl out_args in
                                   let uu____13900 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2220_13864.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2220_13864.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____13865;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____13883;
                                     FStar_Syntax_Syntax.flags = uu____13900
                                   } in
                                 ((let uu___2223_13904 = c in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2223_13904.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2223_13904.FStar_Syntax_Syntax.vars)
                                   }), wl2)) in
                      let uu____13907 =
                        FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu____13907 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____13945 =
                                   imitate_comp bs bs_terms c wl1 in
                                 (match uu____13945 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu____13956 =
                                          let uu____13961 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____13961) in
                                        TERM uu____13956 in
                                      let uu____13962 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu____13962 with
                                       | (sub_prob, wl3) ->
                                           let uu____13975 =
                                             let uu____13976 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu____13976 in
                                           solve env uu____13975))
                             | (x, imp)::formals2 ->
                                 let uu____13998 =
                                   let uu____14005 =
                                     let uu____14008 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____14008
                                       FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14005 wl1 in
                                 (match uu____13998 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu____14029 =
                                          let uu____14032 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some
                                            uu____14032 in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14029 u_x in
                                      let uu____14033 =
                                        let uu____14036 =
                                          let uu____14039 =
                                            let uu____14040 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y in
                                            (uu____14040, imp) in
                                          [uu____14039] in
                                        FStar_List.append bs_terms
                                          uu____14036 in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14033 formals2 wl2) in
                           let uu____14067 = occurs_check u_lhs arrow in
                           (match uu____14067 with
                            | (uu____14078, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14089 =
                                    mklstr
                                      (fun uu____14094 ->
                                         let uu____14095 =
                                           FStar_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14095) in
                                  giveup_or_defer env orig wl uu____14089
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
              (let uu____14124 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____14124
               then
                 let uu____14125 =
                   FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu____14126 =
                   FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14125 (rel_to_string (p_rel orig)) uu____14126
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu____14251 = rhs wl1 scope env1 subst in
                     (match uu____14251 with
                      | (rhs_prob, wl2) ->
                          ((let uu____14273 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu____14273
                            then
                              let uu____14274 = prob_to_string env1 rhs_prob in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____14274
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1, imp)::xs1, (hd2, imp')::ys1) when
                     let uu____14347 = FStar_Syntax_Util.eq_aqual imp imp' in
                     uu____14347 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2293_14349 = hd1 in
                       let uu____14350 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2293_14349.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2293_14349.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14350
                       } in
                     let hd21 =
                       let uu___2296_14354 = hd2 in
                       let uu____14355 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2296_14354.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2296_14354.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____14355
                       } in
                     let uu____14358 =
                       let uu____14363 =
                         FStar_All.pipe_left invert_rel (p_rel orig) in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____14363
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter" in
                     (match uu____14358 with
                      | (prob, wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                          let subst1 =
                            let uu____14384 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____14384 in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                          let uu____14388 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1 in
                          (match uu____14388 with
                           | (env3, FStar_Util.Inl (sub_probs, phi), wl3) ->
                               let phi1 =
                                 let uu____14456 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____14456 in
                               ((let uu____14474 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel") in
                                 if uu____14474
                                 then
                                   let uu____14475 =
                                     FStar_Syntax_Print.term_to_string phi1 in
                                   let uu____14476 =
                                     FStar_Syntax_Print.bv_to_string hd12 in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____14475
                                     uu____14476
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____14505 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1) in
               let uu____14538 = aux wl [] env [] bs1 bs2 in
               match uu____14538 with
               | (env1, FStar_Util.Inr msg, wl1) -> giveup_lit env1 msg orig
               | (env1, FStar_Util.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu____14591 = attempt sub_probs wl2 in
                   solve env1 uu____14591)
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
            let uu___2334_14611 = wl in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2334_14611.wl_deferred_to_tac);
              ctr = (uu___2334_14611.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2334_14611.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2334_14611.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu____14619 = try_solve env wl' in
          match uu____14619 with
          | Success (uu____14620, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____14632 = compress_tprob wl.tcenv problem in
         solve_t' env uu____14632 wl)
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
            let uu____14638 = should_defer_flex_to_user_tac env wl lhs in
            if uu____14638
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____14648 =
                   FStar_List.map FStar_Pervasives_Native.fst bs in
                 FStar_Util.as_set uu____14648 FStar_Syntax_Syntax.order_bv in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____14682 = lhs1 in
                 match uu____14682 with
                 | Flex (uu____14685, ctx_u, uu____14687) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____14695 ->
                           let uu____14696 = sn_binders env1 bs in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____14696 rhs1 in
                     [TERM (ctx_u, sol)] in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____14743 = quasi_pattern env1 lhs1 in
                 match uu____14743 with
                 | FStar_Pervasives_Native.None ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs, uu____14773) ->
                     let uu____14778 = lhs1 in
                     (match uu____14778 with
                      | Flex (t_lhs, ctx_u, args) ->
                          let uu____14792 = occurs_check ctx_u rhs1 in
                          (match uu____14792 with
                           | (uvars, occurs_ok, msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____14834 =
                                   let uu____14841 =
                                     let uu____14842 = FStar_Option.get msg in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____14842 in
                                   FStar_Util.Inl uu____14841 in
                                 (uu____14834, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs) in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1 in
                                  let uu____14864 =
                                    let uu____14865 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs in
                                    Prims.op_Negation uu____14865 in
                                  if uu____14864
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____14885 =
                                       let uu____14892 =
                                         mk_solution env1 lhs1 bs rhs1 in
                                       FStar_Util.Inr uu____14892 in
                                     let uu____14897 =
                                       restrict_all_uvars ctx_u uvars wl1 in
                                     (uu____14885, uu____14897))))) in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____14940 = FStar_Syntax_Util.head_and_args rhs1 in
                 match uu____14940 with
                 | (rhs_hd, args) ->
                     let uu____14983 = FStar_Util.prefix args in
                     (match uu____14983 with
                      | (args_rhs, last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              rhs1.FStar_Syntax_Syntax.pos in
                          let uu____15053 = lhs1 in
                          (match uu____15053 with
                           | Flex (t_lhs, u_lhs, _lhs_args) ->
                               let uu____15057 =
                                 let uu____15068 =
                                   let uu____15075 =
                                     let uu____15078 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____15078 in
                                   copy_uvar u_lhs [] uu____15075 wl1 in
                                 match uu____15068 with
                                 | (uu____15105, t_last_arg, wl2) ->
                                     let uu____15108 =
                                       let uu____15115 =
                                         let uu____15116 =
                                           let uu____15125 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg in
                                           [uu____15125] in
                                         FStar_List.append bs_lhs uu____15116 in
                                       copy_uvar u_lhs uu____15115 t_res_lhs
                                         wl2 in
                                     (match uu____15108 with
                                      | (uu____15160, lhs', wl3) ->
                                          let uu____15163 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3 in
                                          (match uu____15163 with
                                           | (uu____15180, lhs'_last_arg,
                                              wl4) ->
                                               (lhs', lhs'_last_arg, wl4))) in
                               (match uu____15057 with
                                | (lhs', lhs'_last_arg, wl2) ->
                                    let sol =
                                      let uu____15201 =
                                        let uu____15202 =
                                          let uu____15207 =
                                            let uu____15208 =
                                              let uu____15211 =
                                                let uu____15212 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lhs'_last_arg in
                                                [uu____15212] in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                lhs' uu____15211
                                                t_lhs.FStar_Syntax_Syntax.pos in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____15208
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____15207) in
                                        TERM uu____15202 in
                                      [uu____15201] in
                                    let uu____15237 =
                                      let uu____15244 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs" in
                                      match uu____15244 with
                                      | (p1, wl3) ->
                                          let uu____15263 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs" in
                                          (match uu____15263 with
                                           | (p2, wl4) -> ([p1; p2], wl4)) in
                                    (match uu____15237 with
                                     | (sub_probs, wl3) ->
                                         let uu____15294 =
                                           let uu____15295 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3 in
                                           attempt sub_probs uu____15295 in
                                         solve env1 uu____15294)))) in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____15328 = FStar_Syntax_Util.head_and_args rhs2 in
                   match uu____15328 with
                   | (uu____15345, args) ->
                       (match args with | [] -> false | uu____15379 -> true) in
                 let is_arrow rhs2 =
                   let uu____15396 =
                     let uu____15397 = FStar_Syntax_Subst.compress rhs2 in
                     uu____15397.FStar_Syntax_Syntax.n in
                   match uu____15396 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____15400 -> true
                   | uu____15415 -> false in
                 let uu____15416 = quasi_pattern env1 lhs1 in
                 match uu____15416 with
                 | FStar_Pervasives_Native.None ->
                     let msg =
                       mklstr
                         (fun uu____15434 ->
                            let uu____15435 = prob_to_string env1 orig1 in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____15435) in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                     let uu____15442 = is_app rhs1 in
                     if uu____15442
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____15444 = is_arrow rhs1 in
                        if uu____15444
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____15453 ->
                                  let uu____15454 = prob_to_string env1 orig1 in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____15454) in
                           giveup_or_defer env1 orig1 wl1 msg)) in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB ->
                   if wl.defer_ok
                   then
                     let uu____15455 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____15455
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV ->
                   if wl.defer_ok
                   then
                     let uu____15457 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____15457
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ ->
                   let uu____15459 = lhs in
                   (match uu____15459 with
                    | Flex (_t1, ctx_uv, args_lhs) ->
                        let uu____15463 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs in
                        (match uu____15463 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs in
                             let names_to_string1 fvs =
                               let uu____15480 =
                                 let uu____15483 =
                                   FStar_Util.set_elements fvs in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____15483 in
                               FStar_All.pipe_right uu____15480
                                 (FStar_String.concat ", ") in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders) in
                             let fvs2 = FStar_Syntax_Free.names rhs1 in
                             let uu____15500 = occurs_check ctx_uv rhs1 in
                             (match uu____15500 with
                              | (uvars, occurs_ok, msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____15522 =
                                      let uu____15523 =
                                        let uu____15524 =
                                          FStar_Option.get msg in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____15524 in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____15523 in
                                    giveup_or_defer env orig wl uu____15522
                                  else
                                    (let uu____15526 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1 in
                                     if uu____15526
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1 in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars wl in
                                       let uu____15531 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1 in
                                       solve env uu____15531
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____15544 ->
                                                 let uu____15545 =
                                                   names_to_string1 fvs2 in
                                                 let uu____15546 =
                                                   names_to_string1 fvs1 in
                                                 let uu____15547 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders) in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____15545 uu____15546
                                                   uu____15547) in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____15555 ->
                             if wl.defer_ok
                             then
                               let uu____15558 =
                                 FStar_Thunk.mkv "Not a pattern" in
                               giveup_or_defer env orig wl uu____15558
                             else
                               (let uu____15560 =
                                  try_quasi_pattern orig env wl lhs rhs in
                                match uu____15560 with
                                | (FStar_Util.Inr sol, wl1) ->
                                    let uu____15583 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1 in
                                    solve env uu____15583
                                | (FStar_Util.Inl msg, uu____15585) ->
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
                  let uu____15599 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15599
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok
                then
                  let uu____15601 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____15601
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu____15603 =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu____15603
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
                    (let uu____15605 =
                       FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer env orig wl uu____15605)
                  else
                    (let uu____15607 =
                       let uu____15624 = quasi_pattern env lhs in
                       let uu____15631 = quasi_pattern env rhs in
                       (uu____15624, uu____15631) in
                     match uu____15607 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs, t_res_lhs),
                        FStar_Pervasives_Native.Some
                        (binders_rhs, t_res_rhs)) ->
                         let uu____15674 = lhs in
                         (match uu____15674 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____15675;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____15677;_},
                               u_lhs, uu____15679)
                              ->
                              let uu____15682 = rhs in
                              (match uu____15682 with
                               | Flex (uu____15683, u_rhs, uu____15685) ->
                                   let uu____15686 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs) in
                                   if uu____15686
                                   then
                                     let uu____15691 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl in
                                     solve env uu____15691
                                   else
                                     (let uu____15693 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                      match uu____15693 with
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
                                          let uu____15725 =
                                            let uu____15732 =
                                              let uu____15735 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs in
                                              FStar_Syntax_Util.arrow zs
                                                uu____15735 in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____15732
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
                                          (match uu____15725 with
                                           | (uu____15739, w, wl1) ->
                                               let w_app =
                                                 let uu____15743 =
                                                   FStar_List.map
                                                     (fun uu____15754 ->
                                                        match uu____15754
                                                        with
                                                        | (z, uu____15762) ->
                                                            let uu____15767 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____15767) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____15743
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____15769 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____15769
                                                 then
                                                   let uu____15770 =
                                                     let uu____15773 =
                                                       flex_t_to_string lhs in
                                                     let uu____15774 =
                                                       let uu____15777 =
                                                         flex_t_to_string rhs in
                                                       let uu____15778 =
                                                         let uu____15781 =
                                                           term_to_string w in
                                                         let uu____15782 =
                                                           let uu____15785 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____15792 =
                                                             let uu____15795
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____15802
                                                               =
                                                               let uu____15805
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____15805] in
                                                             uu____15795 ::
                                                               uu____15802 in
                                                           uu____15785 ::
                                                             uu____15792 in
                                                         uu____15781 ::
                                                           uu____15782 in
                                                       uu____15777 ::
                                                         uu____15778 in
                                                     uu____15773 ::
                                                       uu____15774 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____15770
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____15811 =
                                                       let uu____15816 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____15816) in
                                                     TERM uu____15811 in
                                                   let uu____15817 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____15817
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____15822 =
                                                          let uu____15827 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____15827) in
                                                        TERM uu____15822 in
                                                      [s1; s2]) in
                                                 let uu____15828 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____15828))))))
                     | uu____15829 ->
                         let uu____15846 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____15846)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____15895 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____15895
            then
              let uu____15896 = FStar_Syntax_Print.term_to_string t1 in
              let uu____15897 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____15898 = FStar_Syntax_Print.term_to_string t2 in
              let uu____15899 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____15896 uu____15897 uu____15898 uu____15899
            else ());
           (let uu____15902 = FStar_Syntax_Util.head_and_args t1 in
            match uu____15902 with
            | (head1, args1) ->
                let uu____15945 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____15945 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____16010 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____16010 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____16014 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____16014) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____16032 =
                         mklstr
                           (fun uu____16043 ->
                              let uu____16044 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____16045 = args_to_string args1 in
                              let uu____16048 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____16049 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____16044 uu____16045 uu____16048
                                uu____16049) in
                       giveup env1 uu____16032 orig
                     else
                       (let uu____16053 =
                          (nargs = Prims.int_zero) ||
                            (let uu____16055 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____16055 = FStar_Syntax_Util.Equal) in
                        if uu____16053
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2607_16057 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2607_16057.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2607_16057.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2607_16057.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2607_16057.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2607_16057.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2607_16057.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2607_16057.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2607_16057.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____16064 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____16064
                                    else solve env1 wl2))
                        else
                          (let uu____16067 = base_and_refinement env1 t1 in
                           match uu____16067 with
                           | (base1, refinement1) ->
                               let uu____16092 = base_and_refinement env1 t2 in
                               (match uu____16092 with
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
                                           let uu____16255 =
                                             FStar_List.fold_right
                                               (fun uu____16295 ->
                                                  fun uu____16296 ->
                                                    match (uu____16295,
                                                            uu____16296)
                                                    with
                                                    | (((a1, uu____16348),
                                                        (a2, uu____16350)),
                                                       (probs, wl3)) ->
                                                        let uu____16399 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____16399
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____16255 with
                                           | (subprobs, wl3) ->
                                               ((let uu____16441 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16441
                                                 then
                                                   let uu____16442 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____16442
                                                 else ());
                                                (let uu____16445 =
                                                   FStar_Options.defensive () in
                                                 if uu____16445
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
                                                    (let uu____16465 =
                                                       mk_sub_probs wl3 in
                                                     match uu____16465 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____16481 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____16481 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____16489 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____16489)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____16513 =
                                                    mk_sub_probs wl3 in
                                                  match uu____16513 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____16529 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____16529 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____16537 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____16537) in
                                         let unfold_and_retry d env2 wl2
                                           uu____16564 =
                                           match uu____16564 with
                                           | (prob, reason) ->
                                               ((let uu____16578 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____16578
                                                 then
                                                   let uu____16579 =
                                                     prob_to_string env2 orig in
                                                   let uu____16580 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____16579 uu____16580
                                                 else ());
                                                (let uu____16582 =
                                                   let uu____16591 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____16594 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____16591, uu____16594) in
                                                 match uu____16582 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____16607 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____16607 with
                                                      | (head1', uu____16625)
                                                          ->
                                                          let uu____16650 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____16650
                                                           with
                                                           | (head2',
                                                              uu____16668) ->
                                                               let uu____16693
                                                                 =
                                                                 let uu____16698
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____16699
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____16698,
                                                                   uu____16699) in
                                                               (match uu____16693
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu____16701
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____16701
                                                                    then
                                                                    let uu____16702
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____16703
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____16704
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____16705
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____16702
                                                                    uu____16703
                                                                    uu____16704
                                                                    uu____16705
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____16707
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2695_16715
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2695_16715.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2695_16715.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2695_16715.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2695_16715.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2695_16715.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2695_16715.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2695_16715.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2695_16715.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
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
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____16718
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____16720 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____16732 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____16732 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____16739 =
                                             let uu____16740 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____16740.FStar_Syntax_Syntax.n in
                                           match uu____16739 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____16744 -> false in
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
                                          | uu____16746 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____16749 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2715_16785 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2715_16785.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2715_16785.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2715_16785.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2715_16785.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2715_16785.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2715_16785.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2715_16785.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2715_16785.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____16860 = destruct_flex_t scrutinee wl1 in
             match uu____16860 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____16871 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____16871 with
                  | (xs, pat_term, uu____16886, uu____16887) ->
                      let uu____16892 =
                        FStar_List.fold_left
                          (fun uu____16915 ->
                             fun x ->
                               match uu____16915 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____16936 = copy_uvar uv [] t_x wl3 in
                                   (match uu____16936 with
                                    | (uu____16955, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____16892 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____16976 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____16976 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2756_16992 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2756_16992.wl_deferred_to_tac);
                                    ctr = (uu___2756_16992.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2756_16992.umax_heuristic_ok);
                                    tcenv = (uu___2756_16992.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2756_16992.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____17000 = solve env1 wl' in
                                (match uu____17000 with
                                 | Success (uu____17003, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2765_17007 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2765_17007.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2765_17007.wl_deferred_to_tac);
                                         ctr = (uu___2765_17007.ctr);
                                         defer_ok =
                                           (uu___2765_17007.defer_ok);
                                         smt_ok = (uu___2765_17007.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2765_17007.umax_heuristic_ok);
                                         tcenv = (uu___2765_17007.tcenv);
                                         wl_implicits =
                                           (uu___2765_17007.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2765_17007.repr_subcomp_allowed)
                                       } in
                                     let uu____17008 = solve env1 wl'1 in
                                     (match uu____17008 with
                                      | Success
                                          (uu____17011, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____17015 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____17015))
                                      | Failed uu____17020 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____17026 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____17047 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____17047
                 then
                   let uu____17048 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____17049 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____17048 uu____17049
                 else ());
                (let uu____17051 =
                   let uu____17072 =
                     let uu____17081 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____17081) in
                   let uu____17088 =
                     let uu____17097 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____17097) in
                   (uu____17072, uu____17088) in
                 match uu____17051 with
                 | ((uu____17126,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____17129;
                       FStar_Syntax_Syntax.vars = uu____17130;_}),
                    (s, t)) ->
                     let uu____17201 =
                       let uu____17202 = is_flex scrutinee in
                       Prims.op_Negation uu____17202 in
                     if uu____17201
                     then
                       ((let uu____17210 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____17210
                         then
                           let uu____17211 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17211
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____17223 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17223
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____17229 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____17229
                           then
                             let uu____17230 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____17231 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____17230 uu____17231
                           else ());
                          (let pat_discriminates uu___26_17252 =
                             match uu___26_17252 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____17267;
                                  FStar_Syntax_Syntax.p = uu____17268;_},
                                FStar_Pervasives_Native.None, uu____17269) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____17282;
                                  FStar_Syntax_Syntax.p = uu____17283;_},
                                FStar_Pervasives_Native.None, uu____17284) ->
                                 true
                             | uu____17309 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____17409 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____17409 with
                                       | (uu____17410, uu____17411, t') ->
                                           let uu____17429 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____17429 with
                                            | (FullMatch, uu____17440) ->
                                                true
                                            | (HeadMatch uu____17453,
                                               uu____17454) -> true
                                            | uu____17467 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____17500 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____17500
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____17505 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____17505 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____17593, uu____17594)
                                       -> branches1
                                   | uu____17739 -> branches in
                                 let uu____17794 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____17803 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____17803 with
                                        | (p, uu____17807, uu____17808) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____17835 ->
                                      FStar_Util.Inr uu____17835) uu____17794))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____17865 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____17865 with
                                | (p, uu____17873, e) ->
                                    ((let uu____17892 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____17892
                                      then
                                        let uu____17893 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____17894 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____17893 uu____17894
                                      else ());
                                     (let uu____17896 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____17909 ->
                                           FStar_Util.Inr uu____17909)
                                        uu____17896)))))
                 | ((s, t),
                    (uu____17912,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____17915;
                       FStar_Syntax_Syntax.vars = uu____17916;_}))
                     ->
                     let uu____17985 =
                       let uu____17986 = is_flex scrutinee in
                       Prims.op_Negation uu____17986 in
                     if uu____17985
                     then
                       ((let uu____17994 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____17994
                         then
                           let uu____17995 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____17995
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18007 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18007
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18013 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18013
                           then
                             let uu____18014 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____18015 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18014 uu____18015
                           else ());
                          (let pat_discriminates uu___26_18036 =
                             match uu___26_18036 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18051;
                                  FStar_Syntax_Syntax.p = uu____18052;_},
                                FStar_Pervasives_Native.None, uu____18053) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18066;
                                  FStar_Syntax_Syntax.p = uu____18067;_},
                                FStar_Pervasives_Native.None, uu____18068) ->
                                 true
                             | uu____18093 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____18193 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____18193 with
                                       | (uu____18194, uu____18195, t') ->
                                           let uu____18213 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____18213 with
                                            | (FullMatch, uu____18224) ->
                                                true
                                            | (HeadMatch uu____18237,
                                               uu____18238) -> true
                                            | uu____18251 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____18284 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____18284
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18289 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____18289 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____18377, uu____18378)
                                       -> branches1
                                   | uu____18523 -> branches in
                                 let uu____18578 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____18587 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____18587 with
                                        | (p, uu____18591, uu____18592) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____18619 ->
                                      FStar_Util.Inr uu____18619) uu____18578))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____18649 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____18649 with
                                | (p, uu____18657, e) ->
                                    ((let uu____18676 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____18676
                                      then
                                        let uu____18677 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____18678 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____18677 uu____18678
                                      else ());
                                     (let uu____18680 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____18693 ->
                                           FStar_Util.Inr uu____18693)
                                        uu____18680)))))
                 | uu____18694 ->
                     ((let uu____18716 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____18716
                       then
                         let uu____18717 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____18718 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____18717 uu____18718
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____18760 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____18760
            then
              let uu____18761 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____18762 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____18763 = FStar_Syntax_Print.term_to_string t1 in
              let uu____18764 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____18761 uu____18762 uu____18763 uu____18764
            else ());
           (let uu____18766 = head_matches_delta env1 wl1 t1 t2 in
            match uu____18766 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____18797, uu____18798) ->
                     let rec may_relate head =
                       let uu____18825 =
                         let uu____18826 = FStar_Syntax_Subst.compress head in
                         uu____18826.FStar_Syntax_Syntax.n in
                       match uu____18825 with
                       | FStar_Syntax_Syntax.Tm_name uu____18829 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____18830 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____18854 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____18854 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____18855 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____18856
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____18857 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____18859, uu____18860) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____18902) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____18908) ->
                           may_relate t
                       | uu____18913 -> false in
                     let uu____18914 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____18914 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____18924 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____18924
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____18930 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____18930
                          then
                            let uu____18931 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____18931 with
                             | (guard, wl2) ->
                                 let uu____18938 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____18938)
                          else
                            (let uu____18940 =
                               mklstr
                                 (fun uu____18951 ->
                                    let uu____18952 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____18953 =
                                      let uu____18954 =
                                        let uu____18957 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____18957
                                          (fun x ->
                                             let uu____18963 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____18963) in
                                      FStar_Util.dflt "" uu____18954 in
                                    let uu____18964 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____18965 =
                                      let uu____18966 =
                                        let uu____18969 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____18969
                                          (fun x ->
                                             let uu____18975 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____18975) in
                                      FStar_Util.dflt "" uu____18966 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____18952 uu____18953 uu____18964
                                      uu____18965) in
                             giveup env1 uu____18940 orig))
                 | (HeadMatch (true), uu____18976) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____18989 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____18989 with
                        | (guard, wl2) ->
                            let uu____18996 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____18996)
                     else
                       (let uu____18998 =
                          mklstr
                            (fun uu____19005 ->
                               let uu____19006 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____19007 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____19006 uu____19007) in
                        giveup env1 uu____18998 orig)
                 | (uu____19008, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2947_19022 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2947_19022.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2947_19022.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2947_19022.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2947_19022.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2947_19022.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2947_19022.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2947_19022.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2947_19022.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____19046 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____19046
          then
            let uu____19047 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____19047
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____19052 =
                let uu____19055 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19055 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____19052 t1);
             (let uu____19073 =
                let uu____19076 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____19076 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____19073 t2);
             (let uu____19094 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____19094
              then
                let uu____19095 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____19096 =
                  let uu____19097 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____19098 =
                    let uu____19099 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____19099 in
                  Prims.op_Hat uu____19097 uu____19098 in
                let uu____19100 =
                  let uu____19101 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____19102 =
                    let uu____19103 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____19103 in
                  Prims.op_Hat uu____19101 uu____19102 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____19095 uu____19096 uu____19100
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____19106, uu____19107) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____19122, FStar_Syntax_Syntax.Tm_delayed uu____19123) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____19138, uu____19139) ->
                  let uu____19166 =
                    let uu___2978_19167 = problem in
                    let uu____19168 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2978_19167.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19168;
                      FStar_TypeChecker_Common.relation =
                        (uu___2978_19167.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2978_19167.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2978_19167.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2978_19167.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2978_19167.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2978_19167.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2978_19167.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2978_19167.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19166 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____19169, uu____19170) ->
                  let uu____19177 =
                    let uu___2984_19178 = problem in
                    let uu____19179 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2984_19178.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____19179;
                      FStar_TypeChecker_Common.relation =
                        (uu___2984_19178.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2984_19178.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2984_19178.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2984_19178.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2984_19178.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2984_19178.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2984_19178.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2984_19178.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19177 wl
              | (uu____19180, FStar_Syntax_Syntax.Tm_ascribed uu____19181) ->
                  let uu____19208 =
                    let uu___2990_19209 = problem in
                    let uu____19210 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2990_19209.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2990_19209.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2990_19209.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19210;
                      FStar_TypeChecker_Common.element =
                        (uu___2990_19209.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2990_19209.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2990_19209.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2990_19209.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2990_19209.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2990_19209.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19208 wl
              | (uu____19211, FStar_Syntax_Syntax.Tm_meta uu____19212) ->
                  let uu____19219 =
                    let uu___2996_19220 = problem in
                    let uu____19221 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2996_19220.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2996_19220.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2996_19220.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____19221;
                      FStar_TypeChecker_Common.element =
                        (uu___2996_19220.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2996_19220.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2996_19220.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2996_19220.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2996_19220.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2996_19220.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____19219 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____19223),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____19225)) ->
                  let uu____19234 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____19234
              | (FStar_Syntax_Syntax.Tm_bvar uu____19235, uu____19236) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____19237, FStar_Syntax_Syntax.Tm_bvar uu____19238) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_19307 =
                    match uu___27_19307 with
                    | [] -> c
                    | bs ->
                        let uu____19335 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____19335 in
                  let uu____19346 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____19346 with
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
                                    let uu____19495 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____19495
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_19580 =
                    match uu___28_19580 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____19622 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____19622 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____19767 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____19768 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____19767
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____19768 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____19769, uu____19770) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____19799 -> true
                    | uu____19818 -> false in
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
                      (let uu____19871 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3098_19879 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3098_19879.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3098_19879.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3098_19879.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3098_19879.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3098_19879.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3098_19879.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3098_19879.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3098_19879.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3098_19879.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3098_19879.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3098_19879.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3098_19879.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3098_19879.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3098_19879.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3098_19879.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3098_19879.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3098_19879.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3098_19879.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3098_19879.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3098_19879.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3098_19879.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3098_19879.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3098_19879.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3098_19879.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3098_19879.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3098_19879.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3098_19879.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3098_19879.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3098_19879.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3098_19879.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3098_19879.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3098_19879.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3098_19879.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3098_19879.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3098_19879.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3098_19879.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3098_19879.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3098_19879.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3098_19879.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3098_19879.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3098_19879.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3098_19879.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3098_19879.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3098_19879.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____19871 with
                       | (uu____19882, ty, uu____19884) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____19893 =
                                 let uu____19894 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____19894.FStar_Syntax_Syntax.n in
                               match uu____19893 with
                               | FStar_Syntax_Syntax.Tm_refine uu____19897 ->
                                   let uu____19904 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____19904
                               | uu____19905 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____19908 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____19908
                             then
                               let uu____19909 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____19910 =
                                 let uu____19911 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____19911 in
                               let uu____19912 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____19909 uu____19910 uu____19912
                             else ());
                            r1)) in
                  let uu____19914 =
                    let uu____19931 = maybe_eta t1 in
                    let uu____19938 = maybe_eta t2 in
                    (uu____19931, uu____19938) in
                  (match uu____19914 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3119_19980 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3119_19980.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3119_19980.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3119_19980.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3119_19980.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3119_19980.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3119_19980.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3119_19980.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3119_19980.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20001 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20001
                       then
                         let uu____20002 = destruct_flex_t not_abs wl in
                         (match uu____20002 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_20017 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_20017.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_20017.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_20017.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_20017.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_20017.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_20017.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_20017.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_20017.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20019 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20019 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20040 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20040
                       then
                         let uu____20041 = destruct_flex_t not_abs wl in
                         (match uu____20041 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_20056 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_20056.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_20056.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_20056.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_20056.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_20056.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_20056.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_20056.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_20056.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20058 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20058 orig))
                   | uu____20059 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____20076, FStar_Syntax_Syntax.Tm_abs uu____20077) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____20106 -> true
                    | uu____20125 -> false in
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
                      (let uu____20178 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3098_20186 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3098_20186.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3098_20186.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3098_20186.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3098_20186.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3098_20186.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3098_20186.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3098_20186.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3098_20186.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3098_20186.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3098_20186.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3098_20186.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3098_20186.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3098_20186.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3098_20186.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3098_20186.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3098_20186.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3098_20186.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3098_20186.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3098_20186.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3098_20186.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3098_20186.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3098_20186.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3098_20186.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3098_20186.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3098_20186.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3098_20186.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3098_20186.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3098_20186.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3098_20186.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3098_20186.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3098_20186.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3098_20186.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3098_20186.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3098_20186.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3098_20186.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3098_20186.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3098_20186.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3098_20186.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3098_20186.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3098_20186.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3098_20186.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3098_20186.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3098_20186.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3098_20186.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____20178 with
                       | (uu____20189, ty, uu____20191) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____20200 =
                                 let uu____20201 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____20201.FStar_Syntax_Syntax.n in
                               match uu____20200 with
                               | FStar_Syntax_Syntax.Tm_refine uu____20204 ->
                                   let uu____20211 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____20211
                               | uu____20212 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____20215 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____20215
                             then
                               let uu____20216 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____20217 =
                                 let uu____20218 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____20218 in
                               let uu____20219 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____20216 uu____20217 uu____20219
                             else ());
                            r1)) in
                  let uu____20221 =
                    let uu____20238 = maybe_eta t1 in
                    let uu____20245 = maybe_eta t2 in
                    (uu____20238, uu____20245) in
                  (match uu____20221 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3119_20287 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3119_20287.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3119_20287.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3119_20287.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3119_20287.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3119_20287.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3119_20287.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3119_20287.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3119_20287.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____20308 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20308
                       then
                         let uu____20309 = destruct_flex_t not_abs wl in
                         (match uu____20309 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_20324 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_20324.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_20324.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_20324.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_20324.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_20324.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_20324.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_20324.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_20324.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20326 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20326 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____20347 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____20347
                       then
                         let uu____20348 = destruct_flex_t not_abs wl in
                         (match uu____20348 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_20363 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_20363.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_20363.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_20363.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_20363.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_20363.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_20363.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_20363.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_20363.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____20365 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____20365 orig))
                   | uu____20366 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____20395 =
                    let uu____20400 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____20400 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3159_20428 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3159_20428.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3159_20428.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3161_20430 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3161_20430.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3161_20430.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____20431, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3159_20445 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3159_20445.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3159_20445.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3161_20447 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3161_20447.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3161_20447.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____20448 -> (x1, x2) in
                  (match uu____20395 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____20467 = as_refinement false env t11 in
                       (match uu____20467 with
                        | (x12, phi11) ->
                            let uu____20474 = as_refinement false env t21 in
                            (match uu____20474 with
                             | (x22, phi21) ->
                                 ((let uu____20482 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____20482
                                   then
                                     ((let uu____20484 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____20485 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____20486 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____20484
                                         uu____20485 uu____20486);
                                      (let uu____20487 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____20488 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____20489 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____20487
                                         uu____20488 uu____20489))
                                   else ());
                                  (let uu____20491 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____20491 with
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
                                         let uu____20559 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____20559
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____20571 =
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
                                         (let uu____20582 =
                                            let uu____20585 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20585 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____20582
                                            (p_guard base_prob));
                                         (let uu____20603 =
                                            let uu____20606 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____20606 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____20603
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____20624 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____20624) in
                                       let has_uvars =
                                         (let uu____20628 =
                                            let uu____20629 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____20629 in
                                          Prims.op_Negation uu____20628) ||
                                           (let uu____20633 =
                                              let uu____20634 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____20634 in
                                            Prims.op_Negation uu____20633) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____20637 =
                                           let uu____20642 =
                                             let uu____20651 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____20651] in
                                           mk_t_problem wl1 uu____20642 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____20637 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____20673 =
                                                solve env1
                                                  (let uu___3204_20675 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3204_20675.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3204_20675.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3204_20675.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3204_20675.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3204_20675.tcenv);
                                                     wl_implicits =
                                                       (uu___3204_20675.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3204_20675.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____20673 with
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
                                                   (uu____20686,
                                                    defer_to_tac,
                                                    uu____20688)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____20693 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____20693 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3220_20702 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3220_20702.attempting);
                                                         wl_deferred =
                                                           (uu___3220_20702.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3220_20702.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3220_20702.defer_ok);
                                                         smt_ok =
                                                           (uu___3220_20702.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3220_20702.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3220_20702.tcenv);
                                                         wl_implicits =
                                                           (uu___3220_20702.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3220_20702.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____20704 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____20704))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20706,
                 FStar_Syntax_Syntax.Tm_uvar uu____20707) ->
                  let uu____20732 = ensure_no_uvar_subst t1 wl in
                  (match uu____20732 with
                   | (t11, wl1) ->
                       let uu____20739 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20739 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20748;
                    FStar_Syntax_Syntax.pos = uu____20749;
                    FStar_Syntax_Syntax.vars = uu____20750;_},
                  uu____20751),
                 FStar_Syntax_Syntax.Tm_uvar uu____20752) ->
                  let uu____20801 = ensure_no_uvar_subst t1 wl in
                  (match uu____20801 with
                   | (t11, wl1) ->
                       let uu____20808 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20808 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20817,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20818;
                    FStar_Syntax_Syntax.pos = uu____20819;
                    FStar_Syntax_Syntax.vars = uu____20820;_},
                  uu____20821)) ->
                  let uu____20870 = ensure_no_uvar_subst t1 wl in
                  (match uu____20870 with
                   | (t11, wl1) ->
                       let uu____20877 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20877 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20886;
                    FStar_Syntax_Syntax.pos = uu____20887;
                    FStar_Syntax_Syntax.vars = uu____20888;_},
                  uu____20889),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____20890;
                    FStar_Syntax_Syntax.pos = uu____20891;
                    FStar_Syntax_Syntax.vars = uu____20892;_},
                  uu____20893)) ->
                  let uu____20966 = ensure_no_uvar_subst t1 wl in
                  (match uu____20966 with
                   | (t11, wl1) ->
                       let uu____20973 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____20973 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____20982, uu____20983) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____20996 = destruct_flex_t t1 wl in
                  (match uu____20996 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21003;
                    FStar_Syntax_Syntax.pos = uu____21004;
                    FStar_Syntax_Syntax.vars = uu____21005;_},
                  uu____21006),
                 uu____21007) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____21044 = destruct_flex_t t1 wl in
                  (match uu____21044 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____21051, FStar_Syntax_Syntax.Tm_uvar uu____21052) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____21065, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21066;
                    FStar_Syntax_Syntax.pos = uu____21067;
                    FStar_Syntax_Syntax.vars = uu____21068;_},
                  uu____21069)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____21106,
                 FStar_Syntax_Syntax.Tm_arrow uu____21107) ->
                  solve_t' env
                    (let uu___3323_21135 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3323_21135.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3323_21135.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3323_21135.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3323_21135.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3323_21135.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3323_21135.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3323_21135.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3323_21135.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3323_21135.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21136;
                    FStar_Syntax_Syntax.pos = uu____21137;
                    FStar_Syntax_Syntax.vars = uu____21138;_},
                  uu____21139),
                 FStar_Syntax_Syntax.Tm_arrow uu____21140) ->
                  solve_t' env
                    (let uu___3323_21192 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3323_21192.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3323_21192.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3323_21192.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3323_21192.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3323_21192.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3323_21192.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3323_21192.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3323_21192.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3323_21192.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21193, FStar_Syntax_Syntax.Tm_uvar uu____21194) ->
                  let uu____21207 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21207
              | (uu____21208, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21209;
                    FStar_Syntax_Syntax.pos = uu____21210;
                    FStar_Syntax_Syntax.vars = uu____21211;_},
                  uu____21212)) ->
                  let uu____21249 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21249
              | (FStar_Syntax_Syntax.Tm_uvar uu____21250, uu____21251) ->
                  let uu____21264 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21264
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____21265;
                    FStar_Syntax_Syntax.pos = uu____21266;
                    FStar_Syntax_Syntax.vars = uu____21267;_},
                  uu____21268),
                 uu____21269) ->
                  let uu____21306 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____21306
              | (FStar_Syntax_Syntax.Tm_refine uu____21307, uu____21308) ->
                  let t21 =
                    let uu____21316 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____21316 in
                  solve_t env
                    (let uu___3358_21342 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3358_21342.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3358_21342.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3358_21342.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3358_21342.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3358_21342.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3358_21342.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3358_21342.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3358_21342.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3358_21342.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____21343, FStar_Syntax_Syntax.Tm_refine uu____21344) ->
                  let t11 =
                    let uu____21352 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____21352 in
                  solve_t env
                    (let uu___3365_21378 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3365_21378.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3365_21378.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3365_21378.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3365_21378.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3365_21378.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3365_21378.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3365_21378.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3365_21378.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3365_21378.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____21460 =
                    let uu____21461 = guard_of_prob env wl problem t1 t2 in
                    match uu____21461 with
                    | (guard, wl1) ->
                        let uu____21468 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____21468 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____21687 = br1 in
                        (match uu____21687 with
                         | (p1, w1, uu____21716) ->
                             let uu____21733 = br2 in
                             (match uu____21733 with
                              | (p2, w2, uu____21756) ->
                                  let uu____21761 =
                                    let uu____21762 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____21762 in
                                  if uu____21761
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____21786 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____21786 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____21823 = br2 in
                                         (match uu____21823 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____21856 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____21856 in
                                              let uu____21861 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____21892,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____21913) ->
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
                                                    let uu____21972 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____21972 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____21861
                                                (fun uu____22043 ->
                                                   match uu____22043 with
                                                   | (wprobs, wl2) ->
                                                       let uu____22080 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____22080
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____22100
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____22100
                                                              then
                                                                let uu____22101
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____22102
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____22101
                                                                  uu____22102
                                                              else ());
                                                             (let uu____22104
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____22104
                                                                (fun
                                                                   uu____22140
                                                                   ->
                                                                   match uu____22140
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
                    | uu____22269 -> FStar_Pervasives_Native.None in
                  let uu____22310 = solve_branches wl brs1 brs2 in
                  (match uu____22310 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____22334 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____22334 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____22359 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____22359 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____22392 =
                                FStar_List.map
                                  (fun uu____22404 ->
                                     match uu____22404 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____22392 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____22413 =
                              let uu____22414 =
                                let uu____22415 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____22415
                                  (let uu___3464_22423 = wl3 in
                                   {
                                     attempting =
                                       (uu___3464_22423.attempting);
                                     wl_deferred =
                                       (uu___3464_22423.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3464_22423.wl_deferred_to_tac);
                                     ctr = (uu___3464_22423.ctr);
                                     defer_ok = (uu___3464_22423.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3464_22423.umax_heuristic_ok);
                                     tcenv = (uu___3464_22423.tcenv);
                                     wl_implicits =
                                       (uu___3464_22423.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3464_22423.repr_subcomp_allowed)
                                   }) in
                              solve env uu____22414 in
                            (match uu____22413 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____22428 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____22435 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____22435 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____22436, uu____22437) ->
                  let head1 =
                    let uu____22461 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22461
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22507 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22507
                      FStar_Pervasives_Native.fst in
                  ((let uu____22553 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22553
                    then
                      let uu____22554 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22555 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22556 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22554 uu____22555 uu____22556
                    else ());
                   (let no_free_uvars t =
                      (let uu____22566 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22566) &&
                        (let uu____22570 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22570) in
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
                      let uu____22586 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22586 = FStar_Syntax_Util.Equal in
                    let uu____22587 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22587
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22588 = equal t1 t2 in
                         (if uu____22588
                          then
                            let uu____22589 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22589
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22592 =
                            let uu____22599 = equal t1 t2 in
                            if uu____22599
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22609 = mk_eq2 wl env orig t1 t2 in
                               match uu____22609 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22592 with
                          | (guard, wl1) ->
                              let uu____22630 = solve_prob orig guard [] wl1 in
                              solve env uu____22630))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____22632, uu____22633) ->
                  let head1 =
                    let uu____22641 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22641
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22687 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22687
                      FStar_Pervasives_Native.fst in
                  ((let uu____22733 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22733
                    then
                      let uu____22734 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22735 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22736 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22734 uu____22735 uu____22736
                    else ());
                   (let no_free_uvars t =
                      (let uu____22746 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22746) &&
                        (let uu____22750 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22750) in
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
                      let uu____22766 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22766 = FStar_Syntax_Util.Equal in
                    let uu____22767 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22767
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22768 = equal t1 t2 in
                         (if uu____22768
                          then
                            let uu____22769 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22769
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22772 =
                            let uu____22779 = equal t1 t2 in
                            if uu____22779
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22789 = mk_eq2 wl env orig t1 t2 in
                               match uu____22789 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22772 with
                          | (guard, wl1) ->
                              let uu____22810 = solve_prob orig guard [] wl1 in
                              solve env uu____22810))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____22812, uu____22813) ->
                  let head1 =
                    let uu____22815 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22815
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____22861 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____22861
                      FStar_Pervasives_Native.fst in
                  ((let uu____22907 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____22907
                    then
                      let uu____22908 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____22909 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____22910 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____22908 uu____22909 uu____22910
                    else ());
                   (let no_free_uvars t =
                      (let uu____22920 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____22920) &&
                        (let uu____22924 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____22924) in
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
                      let uu____22940 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____22940 = FStar_Syntax_Util.Equal in
                    let uu____22941 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____22941
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____22942 = equal t1 t2 in
                         (if uu____22942
                          then
                            let uu____22943 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____22943
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____22946 =
                            let uu____22953 = equal t1 t2 in
                            if uu____22953
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____22963 = mk_eq2 wl env orig t1 t2 in
                               match uu____22963 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____22946 with
                          | (guard, wl1) ->
                              let uu____22984 = solve_prob orig guard [] wl1 in
                              solve env uu____22984))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____22986, uu____22987) ->
                  let head1 =
                    let uu____22989 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____22989
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23035 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23035
                      FStar_Pervasives_Native.fst in
                  ((let uu____23081 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23081
                    then
                      let uu____23082 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23083 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23084 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23082 uu____23083 uu____23084
                    else ());
                   (let no_free_uvars t =
                      (let uu____23094 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23094) &&
                        (let uu____23098 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23098) in
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
                      let uu____23114 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23114 = FStar_Syntax_Util.Equal in
                    let uu____23115 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23115
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23116 = equal t1 t2 in
                         (if uu____23116
                          then
                            let uu____23117 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23117
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23120 =
                            let uu____23127 = equal t1 t2 in
                            if uu____23127
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23137 = mk_eq2 wl env orig t1 t2 in
                               match uu____23137 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23120 with
                          | (guard, wl1) ->
                              let uu____23158 = solve_prob orig guard [] wl1 in
                              solve env uu____23158))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____23160, uu____23161) ->
                  let head1 =
                    let uu____23163 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23163
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23203 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23203
                      FStar_Pervasives_Native.fst in
                  ((let uu____23243 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23243
                    then
                      let uu____23244 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23245 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23246 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23244 uu____23245 uu____23246
                    else ());
                   (let no_free_uvars t =
                      (let uu____23256 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23256) &&
                        (let uu____23260 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23260) in
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
                      let uu____23276 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23276 = FStar_Syntax_Util.Equal in
                    let uu____23277 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23277
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23278 = equal t1 t2 in
                         (if uu____23278
                          then
                            let uu____23279 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23279
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23282 =
                            let uu____23289 = equal t1 t2 in
                            if uu____23289
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23299 = mk_eq2 wl env orig t1 t2 in
                               match uu____23299 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23282 with
                          | (guard, wl1) ->
                              let uu____23320 = solve_prob orig guard [] wl1 in
                              solve env uu____23320))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____23322, uu____23323) ->
                  let head1 =
                    let uu____23341 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23341
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23381 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23381
                      FStar_Pervasives_Native.fst in
                  ((let uu____23421 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23421
                    then
                      let uu____23422 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23423 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23424 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23422 uu____23423 uu____23424
                    else ());
                   (let no_free_uvars t =
                      (let uu____23434 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23434) &&
                        (let uu____23438 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23438) in
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
                      let uu____23454 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23454 = FStar_Syntax_Util.Equal in
                    let uu____23455 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23455
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23456 = equal t1 t2 in
                         (if uu____23456
                          then
                            let uu____23457 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23457
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23460 =
                            let uu____23467 = equal t1 t2 in
                            if uu____23467
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23477 = mk_eq2 wl env orig t1 t2 in
                               match uu____23477 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23460 with
                          | (guard, wl1) ->
                              let uu____23498 = solve_prob orig guard [] wl1 in
                              solve env uu____23498))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23500, FStar_Syntax_Syntax.Tm_match uu____23501) ->
                  let head1 =
                    let uu____23525 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23525
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23565 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23565
                      FStar_Pervasives_Native.fst in
                  ((let uu____23605 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23605
                    then
                      let uu____23606 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23607 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23608 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23606 uu____23607 uu____23608
                    else ());
                   (let no_free_uvars t =
                      (let uu____23618 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23618) &&
                        (let uu____23622 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23622) in
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
                      let uu____23638 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23638 = FStar_Syntax_Util.Equal in
                    let uu____23639 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23639
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23640 = equal t1 t2 in
                         (if uu____23640
                          then
                            let uu____23641 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23641
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23644 =
                            let uu____23651 = equal t1 t2 in
                            if uu____23651
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23661 = mk_eq2 wl env orig t1 t2 in
                               match uu____23661 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23644 with
                          | (guard, wl1) ->
                              let uu____23682 = solve_prob orig guard [] wl1 in
                              solve env uu____23682))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23684, FStar_Syntax_Syntax.Tm_uinst uu____23685) ->
                  let head1 =
                    let uu____23693 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23693
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23733 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23733
                      FStar_Pervasives_Native.fst in
                  ((let uu____23773 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23773
                    then
                      let uu____23774 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23775 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23776 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23774 uu____23775 uu____23776
                    else ());
                   (let no_free_uvars t =
                      (let uu____23786 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23786) &&
                        (let uu____23790 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23790) in
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
                      let uu____23806 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23806 = FStar_Syntax_Util.Equal in
                    let uu____23807 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23807
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23808 = equal t1 t2 in
                         (if uu____23808
                          then
                            let uu____23809 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23809
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23812 =
                            let uu____23819 = equal t1 t2 in
                            if uu____23819
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23829 = mk_eq2 wl env orig t1 t2 in
                               match uu____23829 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23812 with
                          | (guard, wl1) ->
                              let uu____23850 = solve_prob orig guard [] wl1 in
                              solve env uu____23850))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____23852, FStar_Syntax_Syntax.Tm_name uu____23853) ->
                  let head1 =
                    let uu____23855 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____23855
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____23895 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____23895
                      FStar_Pervasives_Native.fst in
                  ((let uu____23935 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____23935
                    then
                      let uu____23936 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____23937 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____23938 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____23936 uu____23937 uu____23938
                    else ());
                   (let no_free_uvars t =
                      (let uu____23948 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____23948) &&
                        (let uu____23952 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____23952) in
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
                      let uu____23968 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____23968 = FStar_Syntax_Util.Equal in
                    let uu____23969 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____23969
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____23970 = equal t1 t2 in
                         (if uu____23970
                          then
                            let uu____23971 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____23971
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____23974 =
                            let uu____23981 = equal t1 t2 in
                            if uu____23981
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____23991 = mk_eq2 wl env orig t1 t2 in
                               match uu____23991 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____23974 with
                          | (guard, wl1) ->
                              let uu____24012 = solve_prob orig guard [] wl1 in
                              solve env uu____24012))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24014, FStar_Syntax_Syntax.Tm_constant uu____24015) ->
                  let head1 =
                    let uu____24017 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24017
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24057 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24057
                      FStar_Pervasives_Native.fst in
                  ((let uu____24097 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24097
                    then
                      let uu____24098 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24099 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24100 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24098 uu____24099 uu____24100
                    else ());
                   (let no_free_uvars t =
                      (let uu____24110 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24110) &&
                        (let uu____24114 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24114) in
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
                      let uu____24130 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24130 = FStar_Syntax_Util.Equal in
                    let uu____24131 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24131
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24132 = equal t1 t2 in
                         (if uu____24132
                          then
                            let uu____24133 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24133
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24136 =
                            let uu____24143 = equal t1 t2 in
                            if uu____24143
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24153 = mk_eq2 wl env orig t1 t2 in
                               match uu____24153 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24136 with
                          | (guard, wl1) ->
                              let uu____24174 = solve_prob orig guard [] wl1 in
                              solve env uu____24174))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24176, FStar_Syntax_Syntax.Tm_fvar uu____24177) ->
                  let head1 =
                    let uu____24179 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24179
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24225 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24225
                      FStar_Pervasives_Native.fst in
                  ((let uu____24271 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24271
                    then
                      let uu____24272 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24273 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24274 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24272 uu____24273 uu____24274
                    else ());
                   (let no_free_uvars t =
                      (let uu____24284 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24284) &&
                        (let uu____24288 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24288) in
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
                      let uu____24304 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24304 = FStar_Syntax_Util.Equal in
                    let uu____24305 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24305
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24306 = equal t1 t2 in
                         (if uu____24306
                          then
                            let uu____24307 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24307
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24310 =
                            let uu____24317 = equal t1 t2 in
                            if uu____24317
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24327 = mk_eq2 wl env orig t1 t2 in
                               match uu____24327 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24310 with
                          | (guard, wl1) ->
                              let uu____24348 = solve_prob orig guard [] wl1 in
                              solve env uu____24348))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____24350, FStar_Syntax_Syntax.Tm_app uu____24351) ->
                  let head1 =
                    let uu____24369 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24369
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24409 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24409
                      FStar_Pervasives_Native.fst in
                  ((let uu____24449 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24449
                    then
                      let uu____24450 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24451 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24452 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24450 uu____24451 uu____24452
                    else ());
                   (let no_free_uvars t =
                      (let uu____24462 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24462) &&
                        (let uu____24466 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24466) in
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
                      let uu____24482 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24482 = FStar_Syntax_Util.Equal in
                    let uu____24483 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24483
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24484 = equal t1 t2 in
                         (if uu____24484
                          then
                            let uu____24485 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24485
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24488 =
                            let uu____24495 = equal t1 t2 in
                            if uu____24495
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24505 = mk_eq2 wl env orig t1 t2 in
                               match uu____24505 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24488 with
                          | (guard, wl1) ->
                              let uu____24526 = solve_prob orig guard [] wl1 in
                              solve env uu____24526))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____24528,
                 FStar_Syntax_Syntax.Tm_let uu____24529) ->
                  let uu____24554 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____24554
                  then
                    let uu____24555 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____24555
                  else
                    (let uu____24557 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____24557 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____24558, uu____24559) ->
                  let uu____24572 =
                    let uu____24577 =
                      let uu____24578 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24579 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24580 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24581 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24578 uu____24579 uu____24580 uu____24581 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24577) in
                  FStar_Errors.raise_error uu____24572
                    t1.FStar_Syntax_Syntax.pos
              | (uu____24582, FStar_Syntax_Syntax.Tm_let uu____24583) ->
                  let uu____24596 =
                    let uu____24601 =
                      let uu____24602 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____24603 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____24604 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____24605 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____24602 uu____24603 uu____24604 uu____24605 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____24601) in
                  FStar_Errors.raise_error uu____24596
                    t1.FStar_Syntax_Syntax.pos
              | uu____24606 ->
                  let uu____24611 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____24611 orig))))
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
          (let uu____24673 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____24673
           then
             let uu____24674 =
               let uu____24675 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____24675 in
             let uu____24676 =
               let uu____24677 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____24677 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____24674 uu____24676
           else ());
          (let uu____24679 =
             let uu____24680 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____24680 in
           if uu____24679
           then
             let uu____24681 =
               mklstr
                 (fun uu____24688 ->
                    let uu____24689 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____24690 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____24689 uu____24690) in
             giveup env uu____24681 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____24708 =
                  mklstr
                    (fun uu____24715 ->
                       let uu____24716 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____24717 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____24716 uu____24717) in
                giveup env uu____24708 orig)
             else
               (let uu____24719 =
                  FStar_List.fold_left2
                    (fun uu____24740 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____24740 with
                           | (univ_sub_probs, wl1) ->
                               let uu____24761 =
                                 let uu____24766 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____24767 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____24766
                                   FStar_TypeChecker_Common.EQ uu____24767
                                   "effect universes" in
                               (match uu____24761 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____24719 with
                | (univ_sub_probs, wl1) ->
                    let uu____24786 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____24786 with
                     | (ret_sub_prob, wl2) ->
                         let uu____24793 =
                           FStar_List.fold_right2
                             (fun uu____24830 ->
                                fun uu____24831 ->
                                  fun uu____24832 ->
                                    match (uu____24830, uu____24831,
                                            uu____24832)
                                    with
                                    | ((a1, uu____24876), (a2, uu____24878),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____24911 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____24911 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____24793 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____24937 =
                                  let uu____24940 =
                                    let uu____24943 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____24943 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____24940 in
                                FStar_List.append univ_sub_probs uu____24937 in
                              let guard =
                                let guard =
                                  let uu____24962 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____24962 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3617_24971 = wl3 in
                                {
                                  attempting = (uu___3617_24971.attempting);
                                  wl_deferred = (uu___3617_24971.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3617_24971.wl_deferred_to_tac);
                                  ctr = (uu___3617_24971.ctr);
                                  defer_ok = (uu___3617_24971.defer_ok);
                                  smt_ok = (uu___3617_24971.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3617_24971.umax_heuristic_ok);
                                  tcenv = (uu___3617_24971.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3617_24971.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____24973 = attempt sub_probs wl5 in
                              solve env uu____24973)))) in
        let solve_layered_sub c11 c21 =
          (let uu____24986 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____24986
           then
             let uu____24987 =
               let uu____24988 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____24988
                 FStar_Syntax_Print.comp_to_string in
             let uu____24989 =
               let uu____24990 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____24990
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____24987 uu____24989
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____24995 =
                 let uu____24996 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____24996 FStar_Ident.string_of_id in
               let uu____24997 =
                 let uu____24998 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____24998 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____24995 uu____24997 in
             let lift_c1 edge =
               let uu____25013 =
                 let uu____25018 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____25018
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____25013
                 (fun uu____25035 ->
                    match uu____25035 with
                    | (c, g) ->
                        let uu____25046 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____25046, g)) in
             let uu____25047 =
               let uu____25058 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____25058 with
               | FStar_Pervasives_Native.None ->
                   let uu____25071 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____25071 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____25087 = lift_c1 edge in
                        (match uu____25087 with
                         | (c12, g_lift) ->
                             let uu____25104 =
                               let uu____25107 =
                                 let uu____25108 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____25108
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____25107
                                 (fun ts ->
                                    let uu____25114 =
                                      let uu____25115 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____25115
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____25114
                                      (fun uu____25126 ->
                                         FStar_Pervasives_Native.Some
                                           uu____25126)) in
                             (c12, g_lift, uu____25104, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____25130 =
                     let uu____25133 =
                       let uu____25134 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____25134
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____25133
                       (fun uu____25145 ->
                          FStar_Pervasives_Native.Some uu____25145) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____25130,
                     true) in
             match uu____25047 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____25156 =
                     mklstr
                       (fun uu____25163 ->
                          let uu____25164 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____25165 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____25164 uu____25165) in
                   giveup env uu____25156 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3652_25171 = wl in
                      {
                        attempting = (uu___3652_25171.attempting);
                        wl_deferred = (uu___3652_25171.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3652_25171.wl_deferred_to_tac);
                        ctr = (uu___3652_25171.ctr);
                        defer_ok = (uu___3652_25171.defer_ok);
                        smt_ok = (uu___3652_25171.smt_ok);
                        umax_heuristic_ok =
                          (uu___3652_25171.umax_heuristic_ok);
                        tcenv = (uu___3652_25171.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3652_25171.repr_subcomp_allowed)
                      } in
                    let uu____25172 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____25194 =
                             let uu____25195 = FStar_Syntax_Subst.compress t in
                             uu____25195.FStar_Syntax_Syntax.n in
                           match uu____25194 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____25198 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____25212)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____25218) ->
                               is_uvar t1
                           | uu____25243 -> false in
                         FStar_List.fold_right2
                           (fun uu____25276 ->
                              fun uu____25277 ->
                                fun uu____25278 ->
                                  match (uu____25276, uu____25277,
                                          uu____25278)
                                  with
                                  | ((a1, uu____25322), (a2, uu____25324),
                                     (is_sub_probs, wl2)) ->
                                      let uu____25357 = is_uvar a1 in
                                      if uu____25357
                                      then
                                        ((let uu____25365 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____25365
                                          then
                                            let uu____25366 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____25367 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____25366 uu____25367
                                          else ());
                                         (let uu____25369 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____25369 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____25172 with
                    | (is_sub_probs, wl2) ->
                        let uu____25395 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____25395 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____25408 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____25409 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____25408 s uu____25409 in
                             let uu____25410 =
                               let uu____25439 =
                                 let uu____25440 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____25440.FStar_Syntax_Syntax.n in
                               match uu____25439 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____25499 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____25499 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____25562 =
                                          let uu____25581 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____25581
                                            (fun uu____25684 ->
                                               match uu____25684 with
                                               | (l1, l2) ->
                                                   let uu____25757 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____25757)) in
                                        (match uu____25562 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____25862 ->
                                   let uu____25863 =
                                     let uu____25868 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____25868) in
                                   FStar_Errors.raise_error uu____25863 r in
                             (match uu____25410 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____25941 =
                                    let uu____25948 =
                                      let uu____25949 =
                                        let uu____25950 =
                                          let uu____25957 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____25957,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____25950 in
                                      [uu____25949] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____25948
                                      (fun b ->
                                         let uu____25973 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____25974 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____25975 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____25973 uu____25974
                                           uu____25975) r in
                                  (match uu____25941 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3717_25983 = wl3 in
                                         {
                                           attempting =
                                             (uu___3717_25983.attempting);
                                           wl_deferred =
                                             (uu___3717_25983.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3717_25983.wl_deferred_to_tac);
                                           ctr = (uu___3717_25983.ctr);
                                           defer_ok =
                                             (uu___3717_25983.defer_ok);
                                           smt_ok = (uu___3717_25983.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3717_25983.umax_heuristic_ok);
                                           tcenv = (uu___3717_25983.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3717_25983.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____26008 =
                                                  let uu____26015 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____26015, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____26008) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____26032 =
                                         let f_sort_is =
                                           let uu____26042 =
                                             let uu____26045 =
                                               let uu____26046 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____26046.FStar_Syntax_Syntax.sort in
                                             let uu____26055 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____26056 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____26045 uu____26055 r
                                               uu____26056 in
                                           FStar_All.pipe_right uu____26042
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____26061 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____26097 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____26097 with
                                                  | (ps, wl5) ->
                                                      ((let uu____26119 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____26119
                                                        then
                                                          let uu____26120 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____26121 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____26120
                                                            uu____26121
                                                        else ());
                                                       (let uu____26123 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____26123
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____26061 in
                                       (match uu____26032 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____26147 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____26147
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____26148 =
                                              let g_sort_is =
                                                let uu____26158 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____26159 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____26158 r uu____26159 in
                                              let uu____26160 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____26196 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____26196 with
                                                       | (ps, wl6) ->
                                                           ((let uu____26218
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____26218
                                                             then
                                                               let uu____26219
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____26220
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____26219
                                                                 uu____26220
                                                             else ());
                                                            (let uu____26222
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____26222
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____26160 in
                                            (match uu____26148 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____26248 =
                                                     let uu____26253 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____26254 =
                                                       let uu____26255 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____26255 in
                                                     (uu____26253,
                                                       uu____26254) in
                                                   match uu____26248 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____26283 =
                                                     let uu____26286 =
                                                       let uu____26289 =
                                                         let uu____26292 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____26292 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____26289 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____26286 in
                                                   ret_sub_prob ::
                                                     uu____26283 in
                                                 let guard =
                                                   let guard =
                                                     let uu____26313 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____26313 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____26324 =
                                                     let uu____26327 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____26330 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____26330)
                                                       uu____26327 in
                                                   solve_prob orig
                                                     uu____26324 [] wl6 in
                                                 let uu____26331 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____26331))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____26356 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____26358 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____26358]
               | x -> x in
             let c12 =
               let uu___3775_26361 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3775_26361.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3775_26361.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3775_26361.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3775_26361.FStar_Syntax_Syntax.flags)
               } in
             let uu____26362 =
               let uu____26367 =
                 FStar_All.pipe_right
                   (let uu___3778_26369 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3778_26369.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3778_26369.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3778_26369.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3778_26369.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____26367
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____26362
               (fun uu____26383 ->
                  match uu____26383 with
                  | (c, g) ->
                      let uu____26390 =
                        let uu____26391 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____26391 in
                      if uu____26390
                      then
                        let uu____26392 =
                          let uu____26397 =
                            let uu____26398 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____26399 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____26398 uu____26399 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____26397) in
                        FStar_Errors.raise_error uu____26392 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____26401 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____26403 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____26403))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____26401
           then
             let uu____26404 =
               mklstr
                 (fun uu____26411 ->
                    let uu____26412 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____26413 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____26412 uu____26413) in
             giveup env uu____26404 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_26419 ->
                        match uu___29_26419 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____26420 -> false)) in
              let uu____26421 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____26451)::uu____26452,
                   (wp2, uu____26454)::uu____26455) -> (wp1, wp2)
                | uu____26528 ->
                    let uu____26553 =
                      let uu____26558 =
                        let uu____26559 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____26560 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____26559 uu____26560 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____26558) in
                    FStar_Errors.raise_error uu____26553
                      env.FStar_TypeChecker_Env.range in
              match uu____26421 with
              | (wpc1, wpc2) ->
                  let uu____26567 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____26567
                  then
                    let uu____26568 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____26568 wl
                  else
                    (let uu____26570 =
                       let uu____26577 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____26577 in
                     match uu____26570 with
                     | (c2_decl, qualifiers) ->
                         let uu____26598 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____26598
                         then
                           let c1_repr =
                             let uu____26602 =
                               let uu____26603 =
                                 let uu____26604 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____26604 in
                               let uu____26605 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26603 uu____26605 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26602 in
                           let c2_repr =
                             let uu____26607 =
                               let uu____26608 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____26609 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____26608 uu____26609 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____26607 in
                           let uu____26610 =
                             let uu____26615 =
                               let uu____26616 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____26617 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____26616 uu____26617 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____26615 in
                           (match uu____26610 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____26621 = attempt [prob] wl2 in
                                solve env uu____26621)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____26638 = lift_c1 () in
                                   FStar_All.pipe_right uu____26638
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____26660 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____26660
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____26664 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____26664 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____26670 =
                                       let uu____26671 =
                                         let uu____26688 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____26691 =
                                           let uu____26702 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____26702; wpc1_2] in
                                         (uu____26688, uu____26691) in
                                       FStar_Syntax_Syntax.Tm_app uu____26671 in
                                     FStar_Syntax_Syntax.mk uu____26670 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____26750 =
                                      let uu____26751 =
                                        let uu____26768 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____26771 =
                                          let uu____26782 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____26791 =
                                            let uu____26802 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____26802; wpc1_2] in
                                          uu____26782 :: uu____26791 in
                                        (uu____26768, uu____26771) in
                                      FStar_Syntax_Syntax.Tm_app uu____26751 in
                                    FStar_Syntax_Syntax.mk uu____26750 r)) in
                            (let uu____26856 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____26856
                             then
                               let uu____26857 =
                                 let uu____26858 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____26858 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____26857
                             else ());
                            (let uu____26860 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____26860 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____26868 =
                                     let uu____26871 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____26874 ->
                                          FStar_Pervasives_Native.Some
                                            uu____26874) uu____26871 in
                                   solve_prob orig uu____26868 [] wl1 in
                                 let uu____26875 = attempt [base_prob] wl2 in
                                 solve env uu____26875))))) in
        let uu____26876 = FStar_Util.physical_equality c1 c2 in
        if uu____26876
        then
          let uu____26877 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____26877
        else
          ((let uu____26880 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____26880
            then
              let uu____26881 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____26882 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____26881
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____26882
            else ());
           (let uu____26884 =
              let uu____26893 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____26896 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____26893, uu____26896) in
            match uu____26884 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____26914),
                    FStar_Syntax_Syntax.Total (t2, uu____26916)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____26933 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____26933 wl
                 | (FStar_Syntax_Syntax.GTotal uu____26934,
                    FStar_Syntax_Syntax.Total uu____26935) ->
                     let uu____26952 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____26952 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____26954),
                    FStar_Syntax_Syntax.Total (t2, uu____26956)) ->
                     let uu____26973 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____26973 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____26975),
                    FStar_Syntax_Syntax.GTotal (t2, uu____26977)) ->
                     let uu____26994 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____26994 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____26996),
                    FStar_Syntax_Syntax.GTotal (t2, uu____26998)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____27015 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____27015 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____27017),
                    FStar_Syntax_Syntax.GTotal (t2, uu____27019)) ->
                     let uu____27036 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____27036 orig
                 | (FStar_Syntax_Syntax.GTotal uu____27037,
                    FStar_Syntax_Syntax.Comp uu____27038) ->
                     let uu____27047 =
                       let uu___3902_27050 = problem in
                       let uu____27053 =
                         let uu____27054 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27054 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3902_27050.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27053;
                         FStar_TypeChecker_Common.relation =
                           (uu___3902_27050.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3902_27050.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3902_27050.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3902_27050.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3902_27050.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3902_27050.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3902_27050.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3902_27050.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27047 wl
                 | (FStar_Syntax_Syntax.Total uu____27055,
                    FStar_Syntax_Syntax.Comp uu____27056) ->
                     let uu____27065 =
                       let uu___3902_27068 = problem in
                       let uu____27071 =
                         let uu____27072 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27072 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3902_27068.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____27071;
                         FStar_TypeChecker_Common.relation =
                           (uu___3902_27068.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3902_27068.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3902_27068.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3902_27068.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3902_27068.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3902_27068.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3902_27068.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3902_27068.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27065 wl
                 | (FStar_Syntax_Syntax.Comp uu____27073,
                    FStar_Syntax_Syntax.GTotal uu____27074) ->
                     let uu____27083 =
                       let uu___3914_27086 = problem in
                       let uu____27089 =
                         let uu____27090 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27090 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3914_27086.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3914_27086.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3914_27086.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27089;
                         FStar_TypeChecker_Common.element =
                           (uu___3914_27086.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3914_27086.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3914_27086.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3914_27086.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3914_27086.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3914_27086.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27083 wl
                 | (FStar_Syntax_Syntax.Comp uu____27091,
                    FStar_Syntax_Syntax.Total uu____27092) ->
                     let uu____27101 =
                       let uu___3914_27104 = problem in
                       let uu____27107 =
                         let uu____27108 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____27108 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3914_27104.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3914_27104.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3914_27104.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____27107;
                         FStar_TypeChecker_Common.element =
                           (uu___3914_27104.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3914_27104.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3914_27104.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3914_27104.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3914_27104.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3914_27104.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____27101 wl
                 | (FStar_Syntax_Syntax.Comp uu____27109,
                    FStar_Syntax_Syntax.Comp uu____27110) ->
                     let uu____27111 =
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
                     if uu____27111
                     then
                       let uu____27112 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____27112 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____27116 =
                            let uu____27121 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____27121
                            then (c1_comp, c2_comp)
                            else
                              (let uu____27127 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____27128 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____27127, uu____27128)) in
                          match uu____27116 with
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
                           (let uu____27135 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____27135
                            then
                              let uu____27136 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____27137 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____27136 uu____27137
                            else ());
                           (let uu____27139 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____27139
                            then solve_layered_sub c12 c22
                            else
                              (let uu____27141 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____27141 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____27144 =
                                     mklstr
                                       (fun uu____27151 ->
                                          let uu____27152 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____27153 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____27152 uu____27153) in
                                   giveup env uu____27144 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____27160 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____27160 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____27201 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____27201 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____27219 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____27247 ->
                match uu____27247 with
                | (u1, u2) ->
                    let uu____27254 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____27255 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____27254 uu____27255)) in
      FStar_All.pipe_right uu____27219 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial, [], (uu____27282, [])) when
          let uu____27307 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____27307 -> "{}"
      | uu____27308 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____27331 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____27331
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____27351 =
              FStar_List.map
                (fun uu____27362 ->
                   match uu____27362 with
                   | (msg, x) ->
                       let uu____27369 =
                         let uu____27370 = prob_to_string env x in
                         Prims.op_Hat ": " uu____27370 in
                       Prims.op_Hat msg uu____27369) defs in
            FStar_All.pipe_right uu____27351 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____27374 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____27375 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____27376 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____27374 uu____27375 uu____27376 imps
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
                  let uu____27429 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____27429
                  then
                    let uu____27430 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____27431 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____27430
                      (rel_to_string rel) uu____27431
                  else "TOP" in
                let uu____27433 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____27433 with
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
              let uu____27491 =
                let uu____27494 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____27497 ->
                     FStar_Pervasives_Native.Some uu____27497) uu____27494 in
              FStar_Syntax_Syntax.new_bv uu____27491 t1 in
            let uu____27498 =
              let uu____27503 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____27503 in
            match uu____27498 with | (p, wl1) -> (p, x, wl1)
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
        (let uu____27574 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____27574
         then
           let uu____27575 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____27575
         else ());
        (let uu____27579 =
           FStar_Util.record_time (fun uu____27585 -> solve env probs) in
         match uu____27579 with
         | (sol, ms) ->
             ((let uu____27597 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____27597
               then
                 let uu____27598 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____27598
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____27611 =
                     FStar_Util.record_time
                       (fun uu____27617 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____27611 with
                    | ((), ms1) ->
                        ((let uu____27628 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____27628
                          then
                            let uu____27629 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____27629
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____27640 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____27640
                     then
                       let uu____27641 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____27641
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
          ((let uu____27665 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____27665
            then
              let uu____27666 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____27666
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____27670 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____27670
             then
               let uu____27671 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____27671
             else ());
            (let f2 =
               let uu____27674 =
                 let uu____27675 = FStar_Syntax_Util.unmeta f1 in
                 uu____27675.FStar_Syntax_Syntax.n in
               match uu____27674 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____27679 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4034_27680 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4034_27680.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4034_27680.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4034_27680.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4034_27680.FStar_TypeChecker_Common.implicits)
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
            let uu____27731 =
              let uu____27732 =
                let uu____27733 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____27734 ->
                       FStar_TypeChecker_Common.NonTrivial uu____27734) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____27733;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____27732 in
            FStar_All.pipe_left
              (fun uu____27741 -> FStar_Pervasives_Native.Some uu____27741)
              uu____27731
let with_guard_no_simp :
  'uuuuuu27750 .
    'uuuuuu27750 ->
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
            let uu____27799 =
              let uu____27800 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____27801 ->
                     FStar_TypeChecker_Common.NonTrivial uu____27801) in
              {
                FStar_TypeChecker_Common.guard_f = uu____27800;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____27799
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
          (let uu____27831 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____27831
           then
             let uu____27832 = FStar_Syntax_Print.term_to_string t1 in
             let uu____27833 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____27832
               uu____27833
           else ());
          (let uu____27835 =
             let uu____27840 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____27840 in
           match uu____27835 with
           | (prob, wl) ->
               let g =
                 let uu____27848 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____27858 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____27848 in
               ((let uu____27880 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____27880
                 then
                   let uu____27881 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____27881
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
        let uu____27898 = try_teq true env t1 t2 in
        match uu____27898 with
        | FStar_Pervasives_Native.None ->
            ((let uu____27902 = FStar_TypeChecker_Env.get_range env in
              let uu____27903 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____27902 uu____27903);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____27910 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____27910
              then
                let uu____27911 = FStar_Syntax_Print.term_to_string t1 in
                let uu____27912 = FStar_Syntax_Print.term_to_string t2 in
                let uu____27913 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____27911
                  uu____27912 uu____27913
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
        (let uu____27933 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____27933
         then
           let uu____27934 = FStar_Syntax_Print.term_to_string t1 in
           let uu____27935 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____27934
             uu____27935
         else ());
        (let uu____27937 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____27937 with
         | (prob, x, wl) ->
             let g =
               let uu____27952 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____27962 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____27952 in
             ((let uu____27984 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____27984
               then
                 let uu____27985 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____27985
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____27990 =
                     let uu____27991 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____27991 g1 in
                   FStar_Pervasives_Native.Some uu____27990)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____28012 = FStar_TypeChecker_Env.get_range env in
          let uu____28013 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____28012 uu____28013
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
        (let uu____28038 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____28038
         then
           let uu____28039 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____28040 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____28039 uu____28040
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____28043 =
           let uu____28050 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____28050 "sub_comp" in
         match uu____28043 with
         | (prob, wl) ->
             let wl1 =
               let uu___4107_28060 = wl in
               {
                 attempting = (uu___4107_28060.attempting);
                 wl_deferred = (uu___4107_28060.wl_deferred);
                 wl_deferred_to_tac = (uu___4107_28060.wl_deferred_to_tac);
                 ctr = (uu___4107_28060.ctr);
                 defer_ok = (uu___4107_28060.defer_ok);
                 smt_ok = (uu___4107_28060.smt_ok);
                 umax_heuristic_ok = (uu___4107_28060.umax_heuristic_ok);
                 tcenv = (uu___4107_28060.tcenv);
                 wl_implicits = (uu___4107_28060.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____28063 =
                 FStar_Util.record_time
                   (fun uu____28074 ->
                      let uu____28075 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____28085 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____28075) in
               match uu____28063 with
               | (r, ms) ->
                   ((let uu____28115 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____28115
                     then
                       let uu____28116 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____28117 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____28118 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____28116 uu____28117
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____28118
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
      fun uu____28147 ->
        match uu____28147 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____28190 =
                 let uu____28195 =
                   let uu____28196 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____28197 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____28196 uu____28197 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____28195) in
               let uu____28198 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____28190 uu____28198) in
            let equiv v v' =
              let uu____28210 =
                let uu____28215 = FStar_Syntax_Subst.compress_univ v in
                let uu____28216 = FStar_Syntax_Subst.compress_univ v' in
                (uu____28215, uu____28216) in
              match uu____28210 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____28239 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____28269 = FStar_Syntax_Subst.compress_univ v in
                      match uu____28269 with
                      | FStar_Syntax_Syntax.U_unif uu____28276 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____28307 ->
                                    match uu____28307 with
                                    | (u, v') ->
                                        let uu____28316 = equiv v v' in
                                        if uu____28316
                                        then
                                          let uu____28319 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____28319 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____28335 -> [])) in
            let uu____28340 =
              let wl =
                let uu___4150_28344 = empty_worklist env in
                {
                  attempting = (uu___4150_28344.attempting);
                  wl_deferred = (uu___4150_28344.wl_deferred);
                  wl_deferred_to_tac = (uu___4150_28344.wl_deferred_to_tac);
                  ctr = (uu___4150_28344.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4150_28344.smt_ok);
                  umax_heuristic_ok = (uu___4150_28344.umax_heuristic_ok);
                  tcenv = (uu___4150_28344.tcenv);
                  wl_implicits = (uu___4150_28344.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4150_28344.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____28362 ->
                      match uu____28362 with
                      | (lb, v) ->
                          let uu____28369 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____28369 with
                           | USolved wl1 -> ()
                           | uu____28371 -> fail lb v))) in
            let rec check_ineq uu____28381 =
              match uu____28381 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____28390) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____28417,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____28419,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____28432) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____28439, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____28447 -> false) in
            let uu____28452 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____28467 ->
                      match uu____28467 with
                      | (u, v) ->
                          let uu____28474 = check_ineq (u, v) in
                          if uu____28474
                          then true
                          else
                            ((let uu____28477 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____28477
                              then
                                let uu____28478 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____28479 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____28478
                                  uu____28479
                              else ());
                             false))) in
            if uu____28452
            then ()
            else
              ((let uu____28483 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____28483
                then
                  ((let uu____28485 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____28485);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____28495 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____28495))
                else ());
               (let uu____28505 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____28505))
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
          let fail uu____28579 =
            match uu____28579 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4228_28604 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4228_28604.attempting);
              wl_deferred = (uu___4228_28604.wl_deferred);
              wl_deferred_to_tac = (uu___4228_28604.wl_deferred_to_tac);
              ctr = (uu___4228_28604.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4228_28604.umax_heuristic_ok);
              tcenv = (uu___4228_28604.tcenv);
              wl_implicits = (uu___4228_28604.wl_implicits);
              repr_subcomp_allowed = (uu___4228_28604.repr_subcomp_allowed)
            } in
          (let uu____28606 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____28606
           then
             let uu____28607 = FStar_Util.string_of_bool defer_ok in
             let uu____28608 = wl_to_string wl in
             let uu____28609 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____28607 uu____28608 uu____28609
           else ());
          (let g1 =
             let uu____28612 = solve_and_commit env wl fail in
             match uu____28612 with
             | FStar_Pervasives_Native.Some
                 (uu____28621::uu____28622, uu____28623, uu____28624) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4245_28654 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4245_28654.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4245_28654.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____28659 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____28671 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____28671
             then
               let uu____28672 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____28672
             else ());
            (let uu___4253_28674 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4253_28674.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4253_28674.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4253_28674.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4253_28674.FStar_TypeChecker_Common.implicits)
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
          (let uu____28749 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____28749
           then
             let uu____28750 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____28750
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4270_28754 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4270_28754.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4270_28754.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4270_28754.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4270_28754.FStar_TypeChecker_Common.implicits)
             } in
           let uu____28755 =
             let uu____28756 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____28756 in
           if uu____28755
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____28764 = FStar_TypeChecker_Env.get_range env in
                      let uu____28765 =
                        let uu____28766 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____28766 in
                      FStar_Errors.diag uu____28764 uu____28765)
                   else ();
                   (let vc1 =
                      let uu____28769 =
                        let uu____28772 =
                          let uu____28773 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____28773 in
                        FStar_Pervasives_Native.Some uu____28772 in
                      FStar_Profiling.profile
                        (fun uu____28775 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____28769 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____28777 = FStar_TypeChecker_Env.get_range env in
                       let uu____28778 =
                         let uu____28779 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____28779 in
                       FStar_Errors.diag uu____28777 uu____28778)
                    else ();
                    (let uu____28782 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____28782 "discharge_guard'" env vc1);
                    (let uu____28783 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____28783 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____28790 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____28791 =
                                 let uu____28792 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____28792 in
                               FStar_Errors.diag uu____28790 uu____28791)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____28797 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____28798 =
                                 let uu____28799 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____28799 in
                               FStar_Errors.diag uu____28797 uu____28798)
                            else ();
                            (let vcs =
                               let uu____28810 = FStar_Options.use_tactics () in
                               if uu____28810
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____28830 ->
                                      (let uu____28832 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____28833 -> ()) uu____28832);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____28876 ->
                                               match uu____28876 with
                                               | (env1, goal, opts) ->
                                                   let uu____28892 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____28892, opts)))))
                               else
                                 (let uu____28894 =
                                    let uu____28901 = FStar_Options.peek () in
                                    (env, vc2, uu____28901) in
                                  [uu____28894]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____28934 ->
                                     match uu____28934 with
                                     | (env1, goal, opts) ->
                                         let uu____28944 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____28944 with
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
                                                 (let uu____28951 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____28952 =
                                                    let uu____28953 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____28954 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____28953 uu____28954 in
                                                  FStar_Errors.diag
                                                    uu____28951 uu____28952)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____28957 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____28958 =
                                                    let uu____28959 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____28959 in
                                                  FStar_Errors.diag
                                                    uu____28957 uu____28958)
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
      let uu____28973 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____28973 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____28980 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____28980
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____28991 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____28991 with
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
        let uu____29017 = try_teq false env t1 t2 in
        match uu____29017 with
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
             let uu____29060 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____29060 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____29070 =
                   let uu____29071 = FStar_Syntax_Subst.compress t_norm in
                   uu____29071.FStar_Syntax_Syntax.n in
                 (match uu____29070 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____29077 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29077
                        (fun uu____29080 ->
                           FStar_Pervasives_Native.Some uu____29080)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____29082) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____29087 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____29087
                        (fun uu____29090 ->
                           FStar_Pervasives_Native.Some uu____29090)
                  | uu____29091 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____29101 =
                      let uu____29102 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____29102 FStar_Util.is_none in
                    if uu____29101
                    then
                      let uu____29107 = imp_value imp in
                      match uu____29107 with
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
        let uu____29128 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____29128 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____29146 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____29146 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____29150 ->
                       let uu____29151 =
                         let uu____29152 = FStar_Syntax_Subst.compress r in
                         uu____29152.FStar_Syntax_Syntax.n in
                       (match uu____29151 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____29156)
                            -> unresolved ctx_u'
                        | uu____29173 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____29193 = acc in
              match uu____29193 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____29200 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____29200 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____29213 = hd in
                       (match uu____29213 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____29219 = unresolved ctx_u in
                               if uu____29219
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____29228 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____29228
                                       then
                                         let uu____29229 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____29229
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____29235 =
                                           teq_nosmt env1 t tm in
                                         match uu____29235 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4415_29244 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4415_29244.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4415_29244.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4415_29244.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4415_29244.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4415_29244.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4415_29244.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4415_29244.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4418_29246 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4418_29246.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4418_29246.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4418_29246.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____29247 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4423_29253 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4423_29253.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4423_29253.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4423_29253.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4423_29253.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4423_29253.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4423_29253.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4423_29253.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4423_29253.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4423_29253.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4423_29253.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4423_29253.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4423_29253.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4423_29253.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4423_29253.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4423_29253.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4423_29253.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4423_29253.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4423_29253.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4423_29253.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4423_29253.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4423_29253.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4423_29253.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4423_29253.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4423_29253.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4423_29253.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4423_29253.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4423_29253.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4423_29253.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4423_29253.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4423_29253.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4423_29253.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4423_29253.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4423_29253.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4423_29253.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4423_29253.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4423_29253.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4423_29253.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4428_29256 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4428_29256.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4428_29256.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4428_29256.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4428_29256.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4428_29256.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4428_29256.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4428_29256.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4428_29256.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4428_29256.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4428_29256.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4428_29256.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4428_29256.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4428_29256.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4428_29256.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4428_29256.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4428_29256.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4428_29256.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4428_29256.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4428_29256.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4428_29256.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4428_29256.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4428_29256.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4428_29256.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4428_29256.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4428_29256.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4428_29256.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4428_29256.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4428_29256.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4428_29256.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4428_29256.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4428_29256.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4428_29256.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____29259 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29259
                                     then
                                       let uu____29260 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____29261 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____29262 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____29263 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____29260 uu____29261 uu____29262
                                         reason uu____29263
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4434_29267 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____29274 =
                                               let uu____29283 =
                                                 let uu____29290 =
                                                   let uu____29291 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____29292 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____29293 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____29291 uu____29292
                                                     uu____29293 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____29290, r) in
                                               [uu____29283] in
                                             FStar_Errors.add_errors
                                               uu____29274);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____29307 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____29317 ->
                                                 let uu____29318 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____29319 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____29320 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____29318 uu____29319
                                                   reason uu____29320)) env2
                                           g1 true in
                                       match uu____29307 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4446_29322 = g in
            let uu____29323 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4446_29322.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4446_29322.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4446_29322.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4446_29322.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____29323
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____29335 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29335
       then
         let uu____29336 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____29336
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
      (let uu____29359 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____29359
       then
         let uu____29360 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____29360
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____29364 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____29365 -> ()) uu____29364
       | imp::uu____29367 ->
           let uu____29370 =
             let uu____29375 =
               let uu____29376 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____29377 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____29376 uu____29377
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____29375) in
           FStar_Errors.raise_error uu____29370
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29393 = teq env t1 t2 in
        force_trivial_guard env uu____29393
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29409 = teq_nosmt env t1 t2 in
        match uu____29409 with
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
          (let uu____29439 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____29439
           then
             let uu____29440 =
               let uu____29441 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____29441
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____29447 = FStar_Syntax_Print.term_to_string t1 in
             let uu____29448 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____29440
               uu____29447 uu____29448
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4484_29460 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4484_29460.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4484_29460.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4484_29460.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4484_29460.FStar_TypeChecker_Common.implicits)
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
        (let uu____29495 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29495
         then
           let uu____29496 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29497 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____29496
             uu____29497
         else ());
        (let uu____29499 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29499 with
         | (prob, x, wl) ->
             let g =
               let uu____29518 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____29528 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29518 in
             ((let uu____29550 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____29550
               then
                 let uu____29551 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____29552 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____29553 =
                   let uu____29554 = FStar_Util.must g in
                   guard_to_string env uu____29554 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____29551 uu____29552 uu____29553
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
        let uu____29588 = check_subtyping env t1 t2 in
        match uu____29588 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29607 =
              let uu____29608 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____29608 g in
            FStar_Pervasives_Native.Some uu____29607
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29626 = check_subtyping env t1 t2 in
        match uu____29626 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____29645 =
              let uu____29646 =
                let uu____29647 = FStar_Syntax_Syntax.mk_binder x in
                [uu____29647] in
              FStar_TypeChecker_Env.close_guard env uu____29646 g in
            FStar_Pervasives_Native.Some uu____29645
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____29684 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____29684
         then
           let uu____29685 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____29686 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____29685
             uu____29686
         else ());
        (let uu____29688 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____29688 with
         | (prob, x, wl) ->
             let g =
               let uu____29703 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____29713 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____29703 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____29738 =
                      let uu____29739 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____29739] in
                    FStar_TypeChecker_Env.close_guard env uu____29738 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____29776 = subtype_nosmt env t1 t2 in
        match uu____29776 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)